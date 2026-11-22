use rayon::prelude::*;
use regex::Regex;
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

pub struct ModuleNode {
    pub name: String,
    pub path: PathBuf,
    pub imports: Vec<String>,
    pub content_hash: u64,
    pub has_heq: bool,
    pub has_heartbeat_hack: bool,
    pub axioms_count: usize,
    pub sorry_count: usize,
    pub trivial_true_count: usize,
}

pub fn strip_lean_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut block_depth = 0usize;

    while i < chars.len() {
        if i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '-' {
            block_depth += 1;
            i += 2;
            continue;
        }
        if block_depth > 0 && i + 1 < chars.len() && chars[i] == '-' && chars[i + 1] == '/' {
            block_depth -= 1;
            i += 2;
            continue;
        }
        if block_depth == 0 && i + 1 < chars.len() && chars[i] == '-' && chars[i + 1] == '-' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if block_depth == 0 {
            out.push(chars[i]);
        }
        i += 1;
    }
    out
}

pub fn normalize_and_hash(text: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty()
            || trimmed.starts_with("--")
            || trimmed.starts_with("import ")
            || trimmed.starts_with("namespace ")
            || trimmed.starts_with("open ")
            || trimmed.starts_with("end ")
        {
            continue;
        }
        for token in trimmed.split_whitespace() {
            token.hash(&mut hasher);
        }
    }
    hasher.finish()
}

pub fn build_dag(src_dir: &Path) -> (usize, HashMap<String, ModuleNode>) {
    let imp_re = Regex::new(r"(?m)^import\s+([A-Za-z0-9_.'«»]+)").unwrap();
    let axiom_re = Regex::new(r"(?m)^(?:private\s+|protected\s+)?axiom\s+").unwrap();
    let sorry_re = Regex::new(r"\b(sorry|admit)\b").unwrap();
    let true_stub_re = Regex::new(r"(?m)^[^|\n]*(?::\s*True\b|∧\s*True\b|/\\\s*True\b|\bTrue\s*(?:∧|/\\)|(?:→|->)\s*True\b)").unwrap();

    let files: Vec<PathBuf> = WalkDir::new(src_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "lean"))
        .map(|e| e.path().to_path_buf())
        .collect();

    let total_files = files.len();

    let nodes: HashMap<String, ModuleNode> = files
        .par_iter()
        .filter_map(|path| {
            let content = fs::read_to_string(path).ok()?;
            let rel = path.strip_prefix(src_dir).ok()?;
            let mod_name = rel.with_extension("").to_string_lossy().replace('/', ".");
            let imports = imp_re
                .captures_iter(&content)
                .filter_map(|c| c.get(1).map(|m| m.as_str().replace(['«', '»'], "")))
                .collect();

            let code_only = strip_lean_comments(&content);

            let content_hash = normalize_and_hash(&content);
            let has_heq = code_only.contains("HEq ");
            let has_heartbeat_hack =
                code_only.contains("maxHeartbeats 0") || code_only.contains("maxHeartbeats 4000000");
            let axioms_count = axiom_re.find_iter(&code_only).count();
            let sorry_count = sorry_re.find_iter(&code_only).count();
            let trivial_true_count = true_stub_re.find_iter(&code_only).count();

            Some((
                mod_name.clone(),
                ModuleNode {
                    name: mod_name,
                    path: path.clone(),
                    imports,
                    content_hash,
                    has_heq,
                    has_heartbeat_hack,
                    axioms_count,
                    sorry_count,
                    trivial_true_count,
                },
            ))
        })
        .collect();

    (total_files, nodes)
}

pub fn find_lake_root(start: &Path) -> Option<PathBuf> {
    let abs = fs::canonicalize(start).unwrap_or_else(|_| start.to_path_buf());
    let mut curr = if abs.is_file() {
        abs.parent()?.to_path_buf()
    } else {
        abs
    };

    loop {
        if curr.join("lakefile.lean").exists() || curr.join("lakefile.toml").exists() {
            return Some(curr);
        }
        if !curr.pop() {
            break;
        }
    }
    None
}

use std::collections::{HashSet, VecDeque};

pub struct ProofDag {
    pub total_files_on_disk: usize,
    pub nodes: HashMap<String, ModuleNode>,
    pub layers: Vec<Vec<String>>,
    #[allow(dead_code)]
    pub clones_skipped: usize,
}

impl ProofDag {
    pub fn build(src_dir: &Path, entry: &str, max_depth: Option<usize>) -> Result<Self, String> {
        let (total_files_on_disk, nodes) = build_dag(src_dir);
        if !nodes.contains_key(entry) {
            return Err(format!("Entry module `{entry}` not found in {:?}", src_dir));
        }

        let mut visited = HashSet::new();
        let mut seen_hashes = HashSet::new();
        let mut queue = VecDeque::new();
        let mut layers: Vec<Vec<String>> = Vec::new();
        let mut clones_skipped = 0usize;

        visited.insert(entry.to_string());
        queue.push_back((entry.to_string(), 0usize));

        while let Some((curr, depth)) = queue.pop_front() {
            if let Some(limit) = max_depth {
                if depth > limit {
                    continue;
                }
            }
            let Some(node) = nodes.get(&curr) else { continue };

            if !seen_hashes.insert(node.content_hash) {
                clones_skipped += 1;
                continue;
            }

            if layers.len() <= depth {
                layers.resize_with(depth + 1, Vec::new);
            }
            layers[depth].push(curr.clone());

            for imp in &node.imports {
                if nodes.contains_key(imp) && visited.insert(imp.clone()) {
                    queue.push_back((imp.clone(), depth + 1));
                }
            }
        }

        Ok(Self {
            total_files_on_disk,
            nodes,
            layers,
            clones_skipped,
        })
    }
}

impl ProofDag {
    /// Строит глобальный пул деклараций по всем модулям этажей `0..=max_layer`
    /// и запускает Fixpoint BFS по графу вызовов начиная с `Depth 0` (и `extra_roots`).
    pub fn collect_used_symbols(&self, max_layer: usize, extra_roots: &[String]) -> HashSet<String> {
        let decl_re = Regex::new(
            r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|@\[[^\]]+\]\s*)*(theorem|lemma|def|structure|inductive|class|instance|abbrev)\s+([A-Za-z0-9_.']+)",
        )
        .unwrap();
        let ident_re = Regex::new(r"\b[A-Za-z_][A-Za-z0-9_']*\b").unwrap();

        let mut symbol_bodies: HashMap<String, Vec<String>> = HashMap::new();
        let mut queue: VecDeque<String> = VecDeque::new();
        let mut used: HashSet<String> = HashSet::new();

        for r in extra_roots {
            if used.insert(r.clone()) {
                queue.push_back(r.clone());
            }
        }

        // 1. Индексируем все декларации со всех этажей 0..=max_layer в единый пул
        for depth in 0..=max_layer {
            let Some(layer) = self.layers.get(depth) else { continue };
            for mod_name in layer {
                let Some(node) = self.nodes.get(mod_name) else { continue };
                let Ok(raw) = fs::read_to_string(&node.path) else { continue };
                let clean = strip_lean_comments(&raw);
                let matches: Vec<_> = decl_re.find_iter(&clean).collect();

                for i in 0..matches.len() {
                    let st = matches[i].start();
                    let en = if i + 1 < matches.len() {
                        matches[i + 1].start()
                    } else {
                        clean.len()
                    };
                    let chunk = &clean[st..en];
                    let short_name = decl_re
                        .captures(chunk)
                        .and_then(|c| c.get(2))
                        .map(|m| m.as_str().rsplit('.').next().unwrap_or(m.as_str()).to_string())
                        .unwrap_or_default();

                    if short_name.is_empty() {
                        continue;
                    }

                    // Всё, что объявлено на 0-м уровне (Main.lean), является корнем поиска
                    if depth == 0 && used.insert(short_name.clone()) {
                        queue.push_back(short_name.clone());
                    }

                    symbol_bodies
                        .entry(short_name)
                        .or_default()
                        .push(chunk.to_string());
                }
            }
        }

        // 2. Fixpoint BFS по графу символов (работает сквозь любые пустые файлы-мосты!)
        while let Some(sym) = queue.pop_front() {
            if let Some(chunks) = symbol_bodies.get(&sym) {
                for chunk in chunks {
                    for m in ident_re.find_iter(chunk) {
                        let tok = m.as_str();
                        let is_generic = matches!(
                            tok,
                            "Refl" | "Symm" | "Trans" | "Congr" | "Card" | "Sum" | "All"

                                | "Unique" | "One" | "Mul" | "Inv" | "Add" | "Zero" | "Mem"
                        );
                        if tok.len() >= 4 && !is_generic && symbol_bodies.contains_key(tok) && used.insert(tok.to_string()) {
                            queue.push_back(tok.to_string());
                        }
                    }
                }
            }
        }

        used
    }
}
