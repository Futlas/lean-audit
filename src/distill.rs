use crate::core::{find_lake_root, strip_lean_comments, ProofDag};
use rayon::prelude::*;
use regex::Regex;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::os::unix::fs as unix_fs;
use std::path::Path;
use std::process::ExitCode;

struct DeclEntry {
    short_name: String,
    chunk: String,
    refs: Vec<String>,
}

fn parse_module_decls(raw: &str) -> (String, Vec<DeclEntry>) {
    let decl_re = Regex::new(
        r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|@\[[^\]]+\]\s*)*(theorem|lemma|def|structure|inductive|class|instance|abbrev)\s+([A-Za-z0-9_.']+)",
    )
    .unwrap();
    let ident_re = Regex::new(r"\b[A-Za-z_][A-Za-z0-9_']*\b").unwrap();

    let matches: Vec<_> = decl_re.find_iter(raw).collect();
    if matches.is_empty() {
        return (raw.to_string(), Vec::new());
    }

    let header = raw[..matches.first().unwrap().start()].to_string();
    let mut decls = Vec::with_capacity(matches.len());

    for i in 0..matches.len() {
        let st = matches[i].start();
        let en = if i + 1 < matches.len() {
            matches[i + 1].start()
        } else {
            raw.len()
        };
        let chunk = &raw[st..en];
        let short_name = decl_re
            .captures(chunk)
            .and_then(|c| c.get(2))
            .map(|m| m.as_str().rsplit('.').next().unwrap_or(m.as_str()).to_string())
            .unwrap_or_default();

        if short_name.is_empty() {
            continue;
        }

        let clean_chunk = strip_lean_comments(chunk);
        let mut refs = Vec::new();
        for m in ident_re.find_iter(&clean_chunk) {
            let tok = m.as_str();
            if tok != short_name && tok.len() >= 4 {
                refs.push(tok.to_string());
            }
        }

        decls.push(DeclEntry {
            short_name,
            chunk: chunk.to_string(),
            refs,
        });
    }

    (header, decls)
}

/// Ленивый кэш транзитивных импортов: вычисляется только для реально посещённых модулей
fn is_module_visible(
    caller: &str,
    target: &str,
    dag: &ProofDag,
    cache: &mut HashMap<String, HashSet<String>>,
) -> bool {
    if caller == target {
        return true;
    }
    if !cache.contains_key(caller) {
        let mut vis = HashSet::new();
        let mut q = VecDeque::new();
        vis.insert(caller.to_string());
        q.push_back(caller.to_string());
        while let Some(curr) = q.pop_front() {
            if let Some(node) = dag.nodes.get(&curr) {
                for imp in &node.imports {
                    if dag.nodes.contains_key(imp) && vis.insert(imp.clone()) {
                        q.push_back(imp.clone());
                    }
                }
            }
        }
        cache.insert(caller.to_string(), vis);
    }
    cache.get(caller).is_some_and(|v| v.contains(target))
}

pub fn run_distill(
    src_dir: &Path,
    entry: &str,
    targets: Vec<String>,
    out_dir: &Path,
    export_stubs: Option<std::path::PathBuf>,
) -> ExitCode {
    let dag = match ProofDag::build(src_dir, entry, None) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Error: {e}");
            return ExitCode::from(2);
        }
    };

    let mut reachable_set = HashSet::new();
    let mut rq = VecDeque::new();
    reachable_set.insert(entry.to_string());
    rq.push_back(entry.to_string());
    while let Some(c) = rq.pop_front() {
        if let Some(n) = dag.nodes.get(&c) {
            for imp in &n.imports {
                if dag.nodes.contains_key(imp) && reachable_set.insert(imp.clone()) {
                    rq.push_back(imp.clone());
                }
            }
        }
    }
    let reachable_mods: Vec<String> = reachable_set.into_iter().collect();

    // 1. Параллельно парсим только достижимые уникальные модули
    let all_modules: Vec<(String, String, Vec<DeclEntry>)> = reachable_mods
        .par_iter()
        .filter_map(|mod_name| {
            let node = dag.nodes.get(mod_name)?;
            let raw = fs::read_to_string(&node.path).ok()?;
            let (header, decls) = parse_module_decls(&raw);
            Some((mod_name.clone(), header, decls))
        })
        .collect();

    let mut total_decls_before = 0usize;
    let mut by_name: HashMap<String, Vec<(usize, usize)>> = HashMap::new();

    for (m_idx, (_, _, decls)) in all_modules.iter().enumerate() {
        total_decls_before += decls.len();
        for (d_idx, d) in decls.iter().enumerate() {
            by_name
                .entry(d.short_name.clone())
                .or_default()
                .push((m_idx, d_idx));
        }
    }

    // 2. Backward Mark с ленивым кэшем видимости
    let mut marked: HashSet<(usize, usize)> = HashSet::new();
    let mut queue: VecDeque<(usize, usize)> = VecDeque::new();
    let mut vis_cache: HashMap<String, HashSet<String>> = HashMap::new();

    for (m_idx, (mod_name, _, decls)) in all_modules.iter().enumerate() {
        for (d_idx, d) in decls.iter().enumerate() {
            let is_seed = if targets.is_empty() {
                mod_name == entry
            } else {
                targets.iter().any(|t| t == &d.short_name)
            };
            if is_seed && marked.insert((m_idx, d_idx)) {
                queue.push_back((m_idx, d_idx));
            }
        }
    }

    while let Some((m_idx, d_idx)) = queue.pop_front() {
        let caller_mod = all_modules[m_idx].0.clone();
        let refs = all_modules[m_idx].2[d_idx].refs.clone();

        for tok in refs {
            if let Some(candidates) = by_name.get(&tok) {
                // Если кандидат один в графе — не нужно даже проверять видимость импортов
                if candidates.len() == 1 {
                    let cand = *candidates.first().unwrap();
                    if marked.insert(cand) {
                        queue.push_back(cand);
                    }
                } else {
                    for &(cand_m, cand_d) in candidates {
                        if marked.contains(&(cand_m, cand_d)) {
                            continue;
                        }
                        let cand_mod = &all_modules[cand_m].0;
                        if is_module_visible(&caller_mod, cand_mod, &dag, &mut vis_cache)
                            && marked.insert((cand_m, cand_d))
                        {
                            queue.push_back((cand_m, cand_d));
                        }
                    }
                }
            }
        }
    }

    // 3. Sweep за O(N) снизу вверх по этажам пирамиды: сохраняем живые модули и файлы-мосты
    let mut live_modules: HashSet<String> = HashSet::new();
    for &(m_idx, _) in &marked {
        live_modules.insert(all_modules[m_idx].0.clone());
    }
    live_modules.insert(entry.to_string());

    let mut bridge_changed = true;
    while bridge_changed {
        bridge_changed = false;
        for mod_name in &reachable_mods {
            if live_modules.contains(mod_name) {
                continue;
            }
            if let Some(node) = dag.nodes.get(mod_name) {
                if node.imports.iter().any(|imp| live_modules.contains(imp)) {
                    live_modules.insert(mod_name.clone());
                    bridge_changed = true;
                }
            }
        }
    }

    // 4. Записываем дистиллированный скелет на диск
    let _ = fs::remove_dir_all(out_dir);
    let out_src = out_dir.join("src");
    let _ = fs::create_dir_all(&out_src);

    let imp_re = Regex::new(r"^import\s+([A-Za-z0-9_.'«»]+)").unwrap();
    let true_re = Regex::new(r"(?::\s*True\b|∧\s*True\b|/\\\s*True\b)").unwrap();

    let mut written_files = 0usize;
    let mut surviving_true_files: Vec<String> = Vec::new();

    for (m_idx, (mod_name, header, decls)) in all_modules.iter().enumerate() {
        if !live_modules.contains(mod_name) {
            continue;
        }
        let Some(node) = dag.nodes.get(mod_name) else { continue };
        let Ok(rel) = node.path.strip_prefix(src_dir) else { continue };

        let mut clean_header = Vec::new();
        for line in header.lines() {
            let trimmed = line.trim();
            if let Some(cap) = imp_re.captures(trimmed) {
                let imp_mod = cap.get(1).unwrap().as_str().replace(['«', '»'], "");
                if !dag.nodes.contains_key(&imp_mod) || live_modules.contains(&imp_mod) {
                    clean_header.push(line.to_string());
                }
            } else {
                clean_header.push(line.to_string());
            }
        }

        let mut body = clean_header.join("\n");
        if !body.ends_with('\n') {
            body.push('\n');
        }

        for (d_idx, d) in decls.iter().enumerate() {
            if marked.contains(&(m_idx, d_idx)) {
                body.push_str(&d.chunk);
            }
        }

        let clean_code = strip_lean_comments(&body);
        if true_re.is_match(&clean_code) {
            surviving_true_files.push(mod_name.clone());
        }

        let dest = out_src.join(rel);
        if let Some(parent) = dest.parent() {
            let _ = fs::create_dir_all(parent);
        }
        if fs::write(&dest, body).is_ok() {
            written_files += 1;
        }
    }

    if let Some(root) = find_lake_root(src_dir) {
        for cfg in ["lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json"] {
            let src_cfg = root.join(cfg);
            if src_cfg.exists() {
                let _ = fs::copy(&src_cfg, out_dir.join(cfg));
            }
        }
        let dot_lake = root.join(".lake");
        if dot_lake.exists() {
            let _ = unix_fs::symlink(&dot_lake, out_dir.join(".lake"));
        }
    }

    println!("\n=== Mark-and-Sweep Proof Distillation (`{entry}`) ===");
    println!(
        "Files: {} on disk -> {} reachable -> {} surviving live files (deleted {} dead files)",
        dag.total_files_on_disk,
        reachable_mods.len(),
        written_files,
        dag.total_files_on_disk.saturating_sub(written_files)
    );
    println!(
        "Declarations: {} total -> {} marked live (pruned {} dead declarations)",
        total_decls_before,
        marked.len(),
        total_decls_before.saturating_sub(marked.len())
    );
    println!(
        "Surviving `: True` stub modules in distilled skeleton: {}",
        surviving_true_files.len()
    );
    if !surviving_true_files.is_empty() {
        for f in surviving_true_files.iter().take(15) {
            println!("  - {f}");
        }
    }
if let Some(ref sp) = export_stubs {
        let paths: Vec<String> = surviving_true_files.iter()
            .filter_map(|m| dag.nodes.get(m)?.path.strip_prefix(src_dir).ok())
            .map(|r| out_src.join(r).to_string_lossy().to_string())
            .collect();
        let _ = fs::write(sp, paths.join("\n"));
        println!("Exported {} stub paths to: {:?}", paths.len(), sp);
    }
    println!("Distilled workspace saved to: {:?}", out_dir);
ExitCode::SUCCESS
}
