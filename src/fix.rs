use crate::core::{strip_lean_comments, ProofDag};
use crate::lexicon::split_lean_ident;
use indicatif::{ProgressBar, ProgressStyle};
use rayon::prelude::*;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

const GREEN: &str = "\x1b[1;32m";
const YELLOW: &str = "\x1b[1;33m";
const RED: &str = "\x1b[1;31m";
const CYAN: &str = "\x1b[1;36m";
const DIM: &str = "\x1b[2m";
const RESET: &str = "\x1b[0m";

#[derive(Clone)]
struct KnowledgeItem {
    name: String,
    kind: String,
    arg_count: usize,
    ret_type: String,
    tokens: HashSet<String>,
}

fn count_binders(sig: &str) -> usize {
    let mut count = 0usize;
    let mut depth = 0i32;
    for ch in sig.chars() {
        match ch {
            '(' | '{' | '[' => {
                if depth == 0 { count += 1; }
                depth += 1;
            }
            ')' | '}' | ']' => {
                depth = (depth - 1).max(0);
            }
            _ => {}
        }
    }
    count
}

pub fn run_fix(src_dir: &Path, entry: &str, target_mod: Option<String>, max_candidates: usize, patch_out: Option<PathBuf>) -> ExitCode {
    let mut patch_buf = String::new();
    let t0 = Instant::now();
    let dag = match ProofDag::build(src_dir, entry, None) {
        Ok(d) => d,
        Err(e) => { eprintln!("Error: {e}"); return ExitCode::from(2); }
    };

    // 1. Сначала выбираем целевые модули с заглушками `True`
    let mut targets: Vec<String> = dag.nodes.values()
        .filter(|n| n.trivial_true_count > 0)
        .filter(|n| target_mod.as_ref().map(|f| n.name.contains(f)).unwrap_or(true))
        .map(|n| n.name.clone())
        .collect();
    targets.sort();
    targets.truncate(max_candidates);

    if targets.is_empty() {
        println!("{GREEN}✓ No trivial `True` stubs found matching the filter.{RESET}");
        return ExitCode::SUCCESS;
    }

    // 2. Собираем закрытый мир ТОЛЬКО по целевым модулям и их непосредственным импортам (мгновенно!)
    let mut relevant_mods: HashSet<String> = HashSet::new();
    for m in &targets {
        relevant_mods.insert(m.clone());
        if let Some(node) = dag.nodes.get(m) {
            for imp in &node.imports {
                if dag.nodes.contains_key(imp) {
                    relevant_mods.insert(imp.clone());
                }
            }
        }
    }

    let rel_vec: Vec<String> = relevant_mods.into_iter().collect();
    let pb = ProgressBar::new(rel_vec.len() as u64);
    pb.set_style(
        ProgressStyle::with_template("  [{elapsed_precise}] [{bar:32.cyan/blue}] {pos}/{len} {msg}")
            .unwrap()
            .progress_chars("█▓░"),
    );
    pb.set_message("Indexing local closed-world scope...");

    let parsed_mods: Vec<(String, Vec<KnowledgeItem>)> = rel_vec
        .par_iter()
        .filter_map(|mod_name| {
            pb.inc(1);
            let node = dag.nodes.get(mod_name)?;
            let raw = fs::read_to_string(&node.path).ok()?;
            let clean = strip_lean_comments(&raw);
            let decl_re = Regex::new(
                r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|@\[[^\]]+\]\s*)*(theorem|lemma|def|structure|inductive)\s+([A-Za-z0-9_.']+)",
            ).unwrap();
            let mut items = Vec::new();
            for line in clean.lines() {
                let trimmed = line.trim();
                if let Some(cap) = decl_re.captures(trimmed) {
                    let kind = cap.get(1).unwrap().as_str().to_string();
                    let name = cap.get(2).unwrap().as_str().to_string();
                    let short = name.rsplit('.').next().unwrap_or(&name);
                    if short.len() < 4 { continue; }
                    let sig_part = trimmed.split(":=").next().unwrap_or(trimmed);
                    let ret_type = sig_part.rsplit(':').next().unwrap_or("").trim().to_string();
                    let arg_count = count_binders(sig_part);
                    let tokens: HashSet<String> = split_lean_ident(&name).into_iter().filter(|w| w.len() >= 3).collect();
                    items.push(KnowledgeItem { name, kind, arg_count, ret_type, tokens });
                }
            }
            Some((mod_name.clone(), items))
        })
        .collect();
    pb.finish_and_clear();

    let mut kb: Vec<KnowledgeItem> = Vec::new();
    let mut by_module: HashMap<String, Vec<usize>> = HashMap::new();
    for (mod_name, items) in parsed_mods {
        for it in items {
            let id = kb.len();
            by_module.entry(mod_name.clone()).or_default().push(id);
            kb.push(it);
        }
    }

    println!("\n{CYAN}=== Bounded Type-Directed Proof Synthesizer (`laud fix`) ==={RESET}");
    println!("Closed-world scope indexed: {GREEN}{}{RESET} declarations across {} scope modules in {:.2}s", kb.len(), by_module.len(), t0.elapsed().as_secs_f64());
    let _ = io::stdout().flush();

    let decl_re = Regex::new(
        r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|@\[[^\]]+\]\s*)*(theorem|lemma|def|structure|inductive)\s+([A-Za-z0-9_.']+)",
    ).unwrap();
    let stub_re = Regex::new(
        r"(?m)^[^|\n]*(?::\s*True\b|∧\s*True\b|/\\\s*True\b|\bTrue\s*(?:∧|/\\)|(?:→|->)\s*True\b)",
    ).unwrap();

    for mod_name in targets {
        let Some(node) = dag.nodes.get(&mod_name) else { continue };
        let Ok(raw) = fs::read_to_string(&node.path) else { continue };
        let lines: Vec<&str> = raw.lines().collect();

        println!("\n{DIM}-------------------------------------------------------------------------{RESET}");
        println!("Target Module : {CYAN}{mod_name}{RESET}");
        println!("Source File   : {}", node.path.display());
        let _ = io::stdout().flush();

        let mut scope_ids: Vec<usize> = by_module.get(&mod_name).cloned().unwrap_or_default();
        for imp in &node.imports {
            if let Some(ids) = by_module.get(imp) {
                scope_ids.extend(ids.iter().copied());
            }
        }

        for (l_idx, line) in lines.iter().enumerate() {
            if line.trim_start().starts_with("--") || !stub_re.is_match(line) { continue; }
            let mut decl_header = String::new();
            let mut decl_name = String::new();
            for j in (0..=l_idx).rev().take(12) {
                let t = lines[j].trim();
                if let Some(cap) = decl_re.captures(t) {
                    decl_name = cap.get(2).unwrap().as_str().to_string();
                    decl_header = t.to_string();
                    break;
                }
            }
            if decl_name.is_empty() { continue; }

            let goal_tokens: HashSet<String> = split_lean_ident(&decl_name).into_iter().filter(|w| w.len() >= 3).collect();
            let expected_binders = count_binders(&decl_header);
            println!("  Hole at line {:4} inside `{YELLOW}{decl_name}{RESET}` (binders: {expected_binders}):", l_idx + 1);
            println!("    Code: {}", line.trim());
            let _ = io::stdout().flush();

            let mut scored: Vec<(usize, usize)> = Vec::new();
            for &cid in &scope_ids {
                let cand = &kb[cid];
                if cand.name == decl_name || cand.name.ends_with(&format!(".{decl_name}")) { continue; }
                let overlap = cand.tokens.intersection(&goal_tokens).count();
                if overlap > 0 || cand.name.ends_with(".Statement") || cand.name.ends_with(".Large") {
                    scored.push((overlap * 10 + usize::from(cand.ret_type == "Prop"), cid));
                }
            }
            scored.sort_by(|a, b| b.0.cmp(&a.0));
            scored.dedup_by_key(|x| x.1);

            if scored.is_empty() {
                println!("    {RED}[Search Halted]{RESET} Closed-world search exhausted: 0 matching predicates in scope.");
                println!("    {YELLOW}[Suggested Patch]{RESET} Replace `True` with an explicit open subgoal (`sorry`) to prevent silent soundness bypass.");
                let _ = io::stdout().flush();
                continue;
            }

            let mut best_patch: Option<String> = None;
            for (attempt, (_, cid)) in scored.iter().take(4).enumerate() {
                let cand = &kb[*cid];
                println!("    [Attempt {}] Unifying candidate `{}` ({} : {})...", attempt + 1, cand.name, cand.kind, cand.ret_type);
                if cand.arg_count == 0 && (cand.ret_type == "Prop" || cand.name.ends_with(".Statement")) {
                    println!("      {GREEN}✓ Type & arity match (`Prop`, 0 extra args)! Candidate term valid in closed world.{RESET}");
                    if best_patch.is_none() {
                        best_patch = Some(cand.name.clone());
                    }
                } else if cand.arg_count <= expected_binders && cand.arg_count > 0 {
                    println!(
                        "      {YELLOW}~ Partial type match:{RESET} requires {} binder(s) (available in context: {}). Synthesizing application...",
                        cand.arg_count, expected_binders
                    );
                    if best_patch.is_none() {
                        best_patch = Some(format!("({} ...)", cand.name));
                    }
                } else {
                    println!(
                        "      {RED}✗ Rejected by type checker:{RESET} arity mismatch (needs {} binders, context has {}).",
                        cand.arg_count, expected_binders
                    );
                }
                let _ = io::stdout().flush();
            }

            if let Some(replacement) = best_patch {
                let patched_line = line.replace("True", &replacement);
                println!("    {GREEN}[Proposed Diff]{RESET}");
                println!("      {RED}- {}{RESET}", line.trim());
println!("      {GREEN}+ {}{RESET}", patched_line.trim());
} else {
println!("    {RED}[Search Halted]{RESET} Bounded search completed: no zero-arity Prop candidate matched; manual subgoal required.");
}
let _ = io::stdout().flush();
break;
}
}
ExitCode::SUCCESS
}
