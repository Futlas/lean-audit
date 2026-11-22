use indicatif::{ProgressBar, ProgressStyle};
use crate::core::{strip_lean_comments, ProofDag};
use regex::Regex;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

struct DeclItem {
    full_name: String,
    short_name: String,
    module: String,
    chunk: String,
    refs: Vec<String>,
}

fn load_module_into(
    m: &str,
    dag: &ProofDag,
    decl_re: &Regex,
    ident_re: &Regex,
    loaded_mods: &mut HashSet<String>,
    ext_imports: &mut HashSet<String>,
    all_decls: &mut Vec<DeclItem>,
    name_idx: &mut HashMap<String, Vec<usize>>,
) -> bool {
    if !loaded_mods.insert(m.to_string()) {
        return false;
    }
    let Some(node) = dag.nodes.get(m) else { return false };
    let Ok(raw) = fs::read_to_string(&node.path) else { return false };

    for line in raw.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("import ") {
            let imp = rest.split_whitespace().next().unwrap_or("");
            if imp.starts_with("Mathlib") || imp.starts_with("Std") || imp.starts_with("Init") {
                ext_imports.insert(t.to_string());
            }
        }
    }

    let matches: Vec<_> = decl_re.find_iter(&raw).collect();
    for i in 0..matches.len() {
        let st = matches[i].start();
        let en = if i + 1 < matches.len() { matches[i + 1].start() } else { raw.len() };
        let chunk = &raw[st..en];
        let full_name = decl_re.captures(chunk).and_then(|c| c.get(2)).map(|x| x.as_str().to_string()).unwrap_or_default();
        let short_name = full_name.rsplit('.').next().unwrap_or(&full_name).to_string();
        if short_name.is_empty() { continue; }
        let clean = strip_lean_comments(chunk);
        let mut refs: Vec<String> = ident_re.find_iter(&clean).map(|x| x.as_str().to_string())
            .filter(|tok| tok != &short_name && tok != &full_name && tok.len() >= 4).collect();
        refs.sort_unstable();
        refs.dedup();
        let id = all_decls.len();
        name_idx.entry(short_name.clone()).or_default().push(id);
        if full_name != short_name {
            name_idx.entry(full_name.clone()).or_default().push(id);
        }
        all_decls.push(DeclItem { full_name, short_name, module: m.to_string(), chunk: chunk.to_string(), refs });
    }
    true
}

pub fn run_flatten(src_dir: &Path, entry: &str, targets: Vec<String>, max_layers: Option<usize>, issue_out: Option<PathBuf>, out_dir: &Path) -> ExitCode {
    let t0 = Instant::now();
    let dag = match ProofDag::build(src_dir, entry, None) {
        Ok(d) => d,
        Err(e) => { eprintln!("Error: {e}"); return ExitCode::from(2); }
    };
    let decl_re = Regex::new(r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|@\[[^\]]+\]\s*)*(theorem|lemma|def|structure|inductive|class|instance|abbrev)\s+([A-Za-z0-9_.']+)").unwrap();
    let ident_re = Regex::new(r"\b[A-Za-z_][A-Za-z0-9_.']*\b").unwrap();

    let mut loaded_mods = HashSet::new();
    let mut expanded_mods: HashSet<String> = HashSet::new();
    let mut ext_imports = HashSet::new();
    let mut all_decls = Vec::new();
    let mut name_idx = HashMap::new();

    load_module_into(entry, &dag, &decl_re, &ident_re, &mut loaded_mods, &mut ext_imports, &mut all_decls, &mut name_idx);

    let mut live_decls: Vec<(usize, usize)> = Vec::new();
    let mut visited: HashSet<usize> = HashSet::new();
    let mut parent_trace: HashMap<usize, usize> = HashMap::new();
    let mut q: VecDeque<(usize, usize)> = VecDeque::new();

    for (id, d) in all_decls.iter().enumerate() {
        let seed = if targets.is_empty() { d.module == entry } else { targets.iter().any(|t| t == &d.short_name || t == &d.full_name) };
        if seed && visited.insert(id) { q.push_back((id, 0)); }
    }

    let pb = ProgressBar::new_spinner();
    pb.set_style(ProgressStyle::with_template("  [{elapsed_precise}] {spinner:.green} {msg}").unwrap());

    while let Some((curr_id, depth)) = q.pop_front() {
        if let Some(lim) = max_layers {
            if depth > lim { continue; }
        }
        if live_decls.len() % 250 == 0 {
            pb.set_message(format!("Tracing layer {} | live decls: {} | modules loaded: {}", depth, live_decls.len(), loaded_mods.len()));
            pb.tick();
        }
        live_decls.push((curr_id, depth));
        let root_m = all_decls[curr_id].module.clone();
        let mut step_q = VecDeque::new();
        if expanded_mods.insert(root_m.clone()) {
            step_q.push_back((root_m, 0usize));
        }
        while let Some((m, d)) = step_q.pop_front() {
            if d > 2 { continue; }
            if let Some(node) = dag.nodes.get(&m) {
                for imp in &node.imports {
                    if dag.nodes.contains_key(imp)
                        && load_module_into(imp, &dag, &decl_re, &ident_re, &mut loaded_mods, &mut ext_imports, &mut all_decls, &mut name_idx)
                    {
                        step_q.push_back((imp.clone(), d + 1));
                    }
                }
            }
        }
        let refs = all_decls[curr_id].refs.clone();
        for tok in refs {
            let tail = tok.rsplit('.').next().unwrap_or(&tok);
            for key in [tok.as_str(), tail] {
                if let Some(cands) = name_idx.get(key) {
                    if cands.len() <= 15 {
                        for &cid in cands {
                            if visited.insert(cid) {
                                parent_trace.insert(cid, curr_id);
                                q.push_back((cid, depth + 1));
                            }
                        }
                    }
                }
            }
        }
    }

    pb.finish_and_clear();
    let max_l = live_decls.iter().map(|&(_, l)| l).max().unwrap_or(0);
    let mut layers: Vec<Vec<usize>> = vec![Vec::new(); max_l + 1];
    for &(id, l) in &live_decls { layers[l].push(id); }

    let _ = fs::remove_dir_all(out_dir);
    let _ = fs::create_dir_all(out_dir);
    let mut ext_list: Vec<String> = if ext_imports.contains("import Mathlib") {
        ext_imports.into_iter().filter(|i| !i.starts_with("import Mathlib.")).collect()
    } else {
        ext_imports.into_iter().collect()
    };
    ext_list.sort();
    let ext_hdr = ext_list.join("\n");
    let true_re = Regex::new(r"(?m)^[^|\n]*(?::\s*True\b|∧\s*True\b|/\\\s*True\b|\bTrue\s*(?:∧|/\\)|(?:→|->)\s*True\b)").unwrap();
    let mut traces: Vec<Vec<String>> = Vec::new();
    let mut stubs = 0usize;

    for (l_idx, ids) in layers.iter().enumerate() {
        let mut body = String::new();
        if l_idx + 1 < layers.len() { body.push_str(&format!("import Layer_{:02}\n", l_idx + 1)); }
        if !ext_hdr.is_empty() { body.push_str(&ext_hdr); body.push('\n'); }
        body.push_str(&format!("\n-- === Layer {} ({} declarations) ===\n\n", l_idx, ids.len()));
        for &id in ids {
            let d = &all_decls[id];
            body.push_str(&format!("-- [from {}]\n{}\n\n", d.module, d.chunk.trim()));
            if true_re.is_match(&strip_lean_comments(&d.chunk)) {
                stubs += 1;
                if traces.len() < 8 {
                    let mut chain = vec![format!("L{:02} {}::{}", l_idx, d.module, d.full_name)];
                    let mut cur = id;
                    while let Some(&p) = parent_trace.get(&cur) {
                        chain.push(format!("{}::{}", all_decls[p].module, all_decls[p].full_name));
                        cur = p;
                    }
                    chain.reverse();
                    traces.push(chain);
                }
            }
        }
        let _ = fs::write(out_dir.join(format!("Layer_{:02}.lean", l_idx)), body);
    }

    println!("\n=== Layered Proof Flattening (`{entry}`) in {:.2}s ===", t0.elapsed().as_secs_f64());
    println!("Disk files: {} -> Loaded modules: {} -> Flat layers: {} (`Layer_00.lean` .. `Layer_{:02}.lean`)", dag.total_files_on_disk, loaded_mods.len(), layers.len(), max_l);
    println!("Live declarations: {} | `: True` stubs in chain: {}", live_decls.len(), stubs);
    for (i, ids) in layers.iter().enumerate() { println!("  Layer_{:02}.lean : {} declarations", i, ids.len()); }
    for (i, tr) in traces.iter().enumerate() {
        println!("\n  ┌─ [Stub Trace #{}]", i + 1);
        for (step_idx, step) in tr.iter().enumerate() {
            let short_step = if step.len() > 88 { format!("…{}", &step[step.len()-87..]) } else { step.clone() };
            if step_idx + 1 == tr.len() {
                println!("  └──▶ [STUB] {short_step}");
            } else {
                println!("  ├─ {short_step}");
            }
        }
    }
    if let Some(ref issue_path) = issue_out {
        let mut md = format!("# Formal Proof Audit Report: `{}`\n\n", entry);
        md.push_str(&format!("- **Total files scanned:** {}\n", dag.total_files_on_disk));
        md.push_str(&format!("- **Live declarations in dependency closure:** {}\n", live_decls.len()));
        md.push_str(&format!("- **Trivial `: True` / `∧ True` / `→ True` stubs detected on critical path:** {}\n\n", stubs));
        md.push_str("## Direct Dependency Chains to Trivial Stubs\n\n");
        for (i, tr) in traces.iter().enumerate() {
            md.push_str(&format!("### Stub Trace #{}\n```text\n{}\n```\n\n", i + 1, tr.join(" ->\n  ")));
        }
        let _ = fs::write(issue_path, md);
        println!("GitHub Issue markdown report saved to: {:?}", issue_path);
    }
    println!("Output saved to: {:?}", out_dir);
    ExitCode::SUCCESS
}
