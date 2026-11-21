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
    let true_stub_re = Regex::new(r"(?::\s*True\b|∧\s*True\b|/\\\s*True\b)").unwrap();

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
