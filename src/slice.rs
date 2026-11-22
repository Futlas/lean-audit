use crate::core::{find_lake_root, strip_lean_comments, ProofDag};
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::os::unix::fs as unix_fs;
use std::path::Path;
use std::process::{Command, ExitCode};

fn split_declarations(raw: &str) -> (String, Vec<(String, String)>) {
    let decl_re = Regex::new(
        r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|@\[[^\]]+\]\s*)*(theorem|lemma|def|structure|inductive|class|instance|abbrev)\s+([A-Za-z0-9_.']+)",
    )
    .unwrap();
    let matches: Vec<_> = decl_re.find_iter(raw).collect();
    if matches.is_empty() {
        return (raw.to_string(), Vec::new());
    }
    let header = raw[..matches.first().unwrap().start()].to_string();
    let mut decls = Vec::new();
    for i in 0..matches.len() {
        let st = matches[i].start();
        let en = if i + 1 < matches.len() { matches[i + 1].start() } else { raw.len() };
        let chunk = &raw[st..en];
        let name = decl_re.captures(chunk).and_then(|c| c.get(2))
            .map(|m| m.as_str().rsplit('.').next().unwrap_or(m.as_str()).to_string())
            .unwrap_or_default();
        decls.push((name, chunk.to_string()));
    }
    (header, decls)
}

fn stub_declaration(chunk: &str) -> String {
    let clean = strip_lean_comments(chunk);
    let head_re = Regex::new(r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|@\[[^\]]+\]\s*)*(theorem|lemma)\b").unwrap();
    if !head_re.is_match(clean.trim_start()) {
        return chunk.to_string();
    }
    if let Some(idx) = chunk.find(":=") {
        let sig = chunk[..idx].trim_end();
        return format!("{sig} := by sorry\n\n");
    }
    chunk.to_string()
}

pub fn run_slice(
    src_dir: &Path,
    entry: &str,
    max_depth: usize,
    out_dir: &Path,
    verify_theorems: Vec<String>,
    tree_shake: bool,
    standalone: bool,
    run: bool,
) -> ExitCode {
    let dag = match ProofDag::build(src_dir, entry, Some(max_depth + 1)) {
        Ok(d) => d,
        Err(e) => { eprintln!("Error: {e}"); return ExitCode::from(2); }
    };
    let used_symbols = if tree_shake {
        if let Ok(full_dag) = ProofDag::build(src_dir, entry, Some(max_depth + 4)) {
            full_dag.collect_used_symbols(full_dag.layers.len(), &verify_theorems)
        } else {
            dag.collect_used_symbols(max_depth + 1, &verify_theorems)
        }
    } else {
        HashSet::new()
    };

    let mut sliced_mods: HashSet<String> = HashSet::new();
    let mut mod_depth: HashMap<String, usize> = HashMap::new();
    for (d, layer) in dag.layers.iter().enumerate() {
        if d > max_depth + 1 { break; }
        for m in layer {
            sliced_mods.insert(m.clone());
            mod_depth.insert(m.clone(), d);
        }
    }

    let _ = fs::remove_dir_all(out_dir);
    let out_src = out_dir.join("src");
    let _ = fs::create_dir_all(&out_src);

    if standalone {
        let prelude = crate::prelude::build_standalone_prelude(&std::collections::HashSet::new());
        let _ = fs::write(out_src.join("StandalonePrelude.lean"), prelude);
    }

    let imp_re = Regex::new(r"^import\s+([A-Za-z0-9_.'«»]+)").unwrap();
    let mut core_files = 0usize;
    let mut boundary_files = 0usize;
    let mut stubbed_theorems = 0usize;

    for mod_name in &sliced_mods {
        let Some(node) = dag.nodes.get(mod_name) else { continue };
        let Ok(raw) = fs::read_to_string(&node.path) else { continue };
        let Ok(rel) = node.path.strip_prefix(src_dir) else { continue };
        let d = *mod_depth.get(mod_name).unwrap_or(&0);
        let is_boundary = d == max_depth + 1;

        let (header, decls) = split_declarations(&raw);
        let mut out_lines = Vec::new();
        if standalone { out_lines.push("module".to_string()); }
        if is_boundary {
            out_lines.push(format!("-- [lean-audit] Auto-generated boundary stub at depth {}", d));
            boundary_files += 1;
        } else {
            core_files += 1;
        }

        for line in header.lines() {
            let trimmed = line.trim();
            if let Some(cap) = imp_re.captures(trimmed) {
                let imp_mod = cap.get(1).unwrap().as_str().replace(['«', '»'], "");
                if dag.nodes.contains_key(&imp_mod) {
                    if sliced_mods.contains(&imp_mod) { if standalone { out_lines.push(format!("public {trimmed}")); } else { out_lines.push(line.to_string()); } }
                } else if standalone {
                    if !out_lines.iter().any(|l| l == "import StandalonePrelude") {
                        out_lines.push("public import StandalonePrelude".to_string());
                    }
                } else {
                    out_lines.push(line.to_string());
                }
            } else if standalone && trimmed.starts_with("open ") {
                let ns_part = trimmed.strip_prefix("open ").unwrap_or("").split(" in ").next().unwrap_or("");
                for ns in ns_part.split_whitespace() {
                    if ns.chars().all(|ch| ch.is_alphanumeric() || ch == '_' || ch == '.') {
                        out_lines.push(format!("namespace {ns} end {ns}"));
                    }
                }
                out_lines.push(line.to_string());
            } else {
                out_lines.push(line.to_string());
            }
        }

        if standalone { out_lines.push("public section".to_string()); }
        let mut body = out_lines.join("\n");
        if !body.ends_with('\n') { body.push('\n'); }
        for (name, chunk) in decls {
            if tree_shake && d > 0 && !used_symbols.contains(&name) { continue; }
            if is_boundary {
                let s = stub_declaration(&chunk);
                if s != chunk { stubbed_theorems += 1; }
                body.push_str(&s);
            } else {
                body.push_str(&chunk);
            }
        }
        let dest = out_src.join(rel);
        if let Some(parent) = dest.parent() { let _ = fs::create_dir_all(parent); }
        let _ = fs::write(&dest, body);
    }

    let lake_root = find_lake_root(src_dir);
    if !standalone {
        if let Some(ref root) = lake_root {
            for cfg in ["lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json"] {
                let src_cfg = root.join(cfg);
                if src_cfg.exists() { let _ = fs::copy(&src_cfg, out_dir.join(cfg)); }
            }
            let dot_lake = root.join(".lake");
            if dot_lake.exists() { let _ = unix_fs::symlink(&dot_lake, out_dir.join(".lake")); }
        }
    }

    let mut verify_code = String::from(if standalone { "module\npublic import StandalonePrelude\n" } else { "" });
    verify_code.push_str(&format!("import {entry}\n"));
    for thm in &verify_theorems {
        verify_code.push_str(&format!("#print axioms {thm}\n"));
    }
    let verify_path = out_src.join("AuditVerify.lean");
    let _ = fs::write(&verify_path, &verify_code);

    println!("\n=== Top-Down Proof Slice (`{entry}`, max_depth={max_depth}) ===");
    println!("Core modules (0..={max_depth}): {core_files} | Boundary stub modules ({}): {boundary_files} | Auto-stubbed theorems: {stubbed_theorems}", max_depth + 1);
    println!("Standalone mode: {standalone} | Slice workspace saved to: {:?}", out_dir);

    if run {
        println!("\nRunning partial kernel verification via `lean`...");
        if standalone {
            let olean_dir = out_dir.join("olean");
            let _ = fs::create_dir_all(&olean_dir);
            let mut build_order: Vec<(usize, String)> = Vec::new();
            build_order.push((usize::MAX, "StandalonePrelude".to_string()));
            for m in &sliced_mods {
                let d = *mod_depth.get(m).unwrap_or(&0);
                build_order.push((d, m.clone()));
            }
            build_order.sort_by(|a, b| b.0.cmp(&a.0));

            let pb = indicatif::ProgressBar::new(build_order.len() as u64);
            pb.set_style(
                indicatif::ProgressStyle::with_template("  [{elapsed_precise}] [{bar:32.green/blue}] {pos}/{len} {msg}")
                    .unwrap()
                    .progress_chars("█▓░"),
            );

            for (_, mod_name) in &build_order {
                pb.set_message(format!("Compiling {mod_name}..."));
                let rel_lean = format!("{}.lean", mod_name.replace('.', "/"));
                let rel_olean = format!("{}.olean", mod_name.replace('.', "/"));
                let _lean_file = out_src.join(&rel_lean);
                let olean_file = olean_dir.join(&rel_olean);
                if let Some(p) = olean_file.parent() { let _ = fs::create_dir_all(p); }
                let step = Command::new("lean")
                    .current_dir(&out_src)
                    .env("LEAN_PATH", &olean_dir)
                    .arg(&rel_lean)
                    .arg("-o")
                    .arg(&olean_file)
                    .output();
                if let Ok(res) = step {
                    if !res.status.success() {
                        pb.finish_and_clear();
                        eprintln!("--- Lean Compilation Error in `{mod_name}` ---");
                        eprintln!("{}", String::from_utf8_lossy(&res.stdout));
                        eprintln!("{}", String::from_utf8_lossy(&res.stderr));
                        return ExitCode::from(1);
                    }
                }
                pb.inc(1);
            }
            pb.finish_and_clear();
        }

        let mut cmd = if !standalone && lake_root.is_some() {
            let mut c = Command::new("lake");
            c.args(["env", "lean"]).current_dir(out_dir);
            c
        } else {
            let mut c = Command::new("lean");
            c.env("LEAN_PATH", out_dir.join("olean"));
            c
        };
        let out = cmd.arg(&verify_path).output();
        match out {
            Ok(res) => {
                let stdout = String::from_utf8_lossy(&res.stdout);
                let stderr = String::from_utf8_lossy(&res.stderr);
                if !stdout.trim().is_empty() { println!("--- Lean Output ---\n{}", stdout.trim()); }
                if !stderr.trim().is_empty() { println!("--- Lean Diagnostics ---\n{}", stderr.trim()); }
                if res.status.success() {
                    println!("SLICE VERIFICATION PASSED: Top {} layers compiled cleanly!", max_depth + 1);
                    return ExitCode::SUCCESS;
                } else {
                    eprintln!("SLICE VERIFICATION FAILED (exit code {:?}).", res.status.code());
                    return ExitCode::from(1);
                }
            }
            Err(e) => { eprintln!("Failed to execute Lean: {e}"); return ExitCode::from(2); }
        }
    }
    ExitCode::SUCCESS
}
