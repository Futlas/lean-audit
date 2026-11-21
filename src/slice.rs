use crate::core::{find_lake_root, ProofDag};
use regex::Regex;
use std::collections::HashSet;
use std::fs;
use std::os::unix::fs as unix_fs;
use std::path::Path;
use std::process::{Command, ExitCode};

fn split_declarations(text: &str) -> (&str, Vec<(String, String)>) {
    let decl_re = Regex::new(
        r"(?m)^(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]+\]\s*)*(theorem|lemma|def|structure|inductive|class|instance|abbrev)\s+([A-Za-z0-9_.']+)",
    )
    .unwrap();

    let matches: Vec<_> = decl_re.find_iter(text).collect();
    if matches.is_empty() {
        return (text, Vec::new());
    }

    let header = &text[..matches[0].start()];
    let mut decls = Vec::with_capacity(matches.len());

    for i in 0..matches.len() {
        let start = matches[i].start();
        let end = if i + 1 < matches.len() {
            matches[i + 1].start()
        } else {
            text.len()
        };
        let chunk = &text[start..end];
        let name = decl_re
            .captures(chunk)
            .and_then(|c| c.get(2))
            .map(|m| m.as_str().rsplit('.').next().unwrap_or(m.as_str()).to_string())
            .unwrap_or_default();
        decls.push((name, chunk.to_string()));
    }

    (header, decls)
}

fn stub_single_theorem(decl_text: &str) -> String {
    let trimmed_start = decl_text.trim_start();
    let is_thm = trimmed_start.starts_with("theorem ")
        || trimmed_start.starts_with("lemma ")
        || trimmed_start.contains(" theorem ")
        || trimmed_start.contains(" lemma ");
    if !is_thm {
        return decl_text.to_string();
    }

    let mut dp = 0usize;
    let mut db = 0usize;
    let mut dc = 0usize;
    let mut i = 0usize;

    while i < decl_text.len() {
        let ch = decl_text[i..].chars().next().unwrap();
        match ch {
            '(' => dp += 1,
            ')' => dp = dp.saturating_sub(1),
            '[' => db += 1,
            ']' => db = db.saturating_sub(1),
            '{' => dc += 1,
            '}' => dc = dc.saturating_sub(1),
            ':' if dp == 0 && db == 0 && dc == 0 => {
                if decl_text[i..].starts_with(":=") {
                    let after = decl_text[i + 2..].trim_start();
                    if after.starts_with("by") {
                        let by_end = decl_text.len() - after.len() + 2;
                        return format!("{} sorry\n\n", &decl_text[..by_end]);
                    }
                    return format!("{}:= sorry\n\n", &decl_text[..i]);
                }
            }
            _ => {}
        }
        i += ch.len_utf8();
    }

    decl_text.to_string()
}

fn process_module(
    content: &str,
    is_boundary: bool,
    allowed_imports: &HashSet<String>,
    used_symbols: Option<&HashSet<String>>,
) -> (String, usize, usize) {
    let imp_re = Regex::new(r"^import\s+([A-Za-z0-9_.'«»]+)").unwrap();
    let (header, decls) = split_declarations(content);

    let mut out_header = Vec::new();
    for line in header.lines() {
        let trimmed = line.trim();
        if let Some(cap) = imp_re.captures(trimmed) {
            let mod_name = cap.get(1).unwrap().as_str().replace(['«', '»'], "");
            let is_external = !mod_name.starts_with("Development.")
                && !mod_name.starts_with("Formalism.")
                && !mod_name.starts_with("Supplements.")
                && !allowed_imports.contains(&mod_name);
            if !is_boundary || is_external || allowed_imports.contains(&mod_name) {
                out_header.push(line.to_string());
            } else {
                out_header.push(format!("-- [laud slice pruned deeper import]: {trimmed}"));
            }
        } else {
            out_header.push(line.to_string());
        }
    }

    let mut out_body = out_header.join("\n");
    if !out_body.ends_with('\n') {
        out_body.push('\n');
    }

    let mut kept = 0usize;
    let mut pruned = 0usize;

    for (name, chunk) in decls {
        if let Some(used) = used_symbols {
            if !name.is_empty() && !used.contains(&name) {
                pruned += 1;
                continue;
            }
        }
        kept += 1;
        if is_boundary {
            out_body.push_str(&stub_single_theorem(&chunk));
        } else {
            out_body.push_str(&chunk);
        }
    }

    (out_body, kept, pruned)
}

pub fn run_slice(
    src_dir: &Path,
    entry: &str,
    max_depth: usize,
    out_dir: &Path,
    verify_theorems: Vec<String>,
    tree_shake: bool,
    run: bool,
) -> ExitCode {
    let dag = match ProofDag::build(src_dir, entry, Some(max_depth + 1)) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Error: {e}");
            return ExitCode::from(2);
        }
    };

    let used_symbols = if tree_shake {
        if let Ok(full_dag) = ProofDag::build(src_dir, entry, None) {
            full_dag.collect_used_symbols(full_dag.layers.len(), &verify_theorems)
        } else {
            dag.collect_used_symbols(max_depth + 1, &verify_theorems)
        }
    } else {
        HashSet::new()
    };

    let _ = fs::remove_dir_all(out_dir);
    let out_src = out_dir.join("src");
    if let Err(e) = fs::create_dir_all(&out_src) {
        eprintln!("Failed to create output workspace {:?}: {e}", out_src);
        return ExitCode::from(2);
    }

    let mut allowed_for_boundary = HashSet::new();
    let mut full_copied = 0usize;
    let mut stubbed_boundary = 0usize;
    let mut total_kept_decls = 0usize;
    let mut total_pruned_decls = 0usize;

    let sym_filter = if tree_shake { Some(&used_symbols) } else { None };

    for depth in 0..=max_depth {
        if let Some(layer) = dag.layers.get(depth) {
            for mod_name in layer {
                allowed_for_boundary.insert(mod_name.clone());
                if let Some(node) = dag.nodes.get(mod_name) {
                    if let (Ok(rel), Ok(raw)) = (node.path.strip_prefix(src_dir), fs::read_to_string(&node.path)) {
                        let dest = out_src.join(rel);
                        if let Some(parent) = dest.parent() {
                            let _ = fs::create_dir_all(parent);
                        }
                        let (processed, kept, pruned) =
                            process_module(&raw, false, &allowed_for_boundary, sym_filter);
                        total_kept_decls += kept;
                        total_pruned_decls += pruned;
                        if fs::write(&dest, processed).is_ok() {
                            full_copied += 1;
                        }
                    }
                }
            }
        }
    }

    if let Some(boundary_layer) = dag.layers.get(max_depth + 1) {
        for mod_name in boundary_layer {
            if let Some(node) = dag.nodes.get(mod_name) {
                if let (Ok(rel), Ok(raw)) = (node.path.strip_prefix(src_dir), fs::read_to_string(&node.path)) {
                    let dest = out_src.join(rel);
                    if let Some(parent) = dest.parent() {
                        let _ = fs::create_dir_all(parent);
                    }
                    let (stubbed, kept, pruned) =
                        process_module(&raw, true, &allowed_for_boundary, sym_filter);
                    total_kept_decls += kept;
                    total_pruned_decls += pruned;
                    if fs::write(&dest, stubbed).is_ok() {
                        stubbed_boundary += 1;
                    }
                }
            }
        }
    }

    let lake_root = find_lake_root(src_dir);
    if let Some(ref root) = lake_root {
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

    let mut verify_code = format!("import {entry}\n\n");
    for thm in &verify_theorems {
        verify_code.push_str(&format!("#print axioms {thm}\n"));
    }
    let verify_file = out_src.join("AuditVerify.lean");
    let _ = fs::write(&verify_file, &verify_code);

    println!("\n=== Partial Verification Slice (`{entry}`, max_depth = {max_depth}) ===");
    println!(
        "Original disk files: {} | Full modules (0..={}): {} | Boundary stubs ({}): {}",
        dag.total_files_on_disk, max_depth, full_copied, max_depth + 1, stubbed_boundary
    );
    if tree_shake {
        println!(
            "Tree-shaking enabled: kept {} used declarations | pruned {} unused declarations",
            total_kept_decls, total_pruned_decls
        );
    }
    println!("Sandbox generated at: {:?}", out_dir);

    if run {
        println!("\nRunning Lean kernel type-check on `AuditVerify.lean`...");
        let output = if lake_root.is_some() {
            Command::new("lake")
                .args(["env", "lean", "src/AuditVerify.lean"])
                .current_dir(out_dir)
                .output()
        } else {
            Command::new("lean").arg(&verify_file).output()
        };

        match output {
            Ok(out) => {
                let stdout = String::from_utf8_lossy(&out.stdout);
                let stderr = String::from_utf8_lossy(&out.stderr);
                if !stdout.is_empty() {
                    println!("--- Lean Output ---\n{stdout}");
                }
                if !stderr.is_empty() {
                    eprintln!("--- Lean Diagnostics ---\n{stderr}");
                }
                if out.status.success() {
                    println!("SLICE VERIFICATION PASSED!");
                    return ExitCode::SUCCESS;
                } else {
                    eprintln!("SLICE VERIFICATION FAILED.");
                    return ExitCode::from(1);
                }
            }
            Err(e) => {
                eprintln!("Failed to execute Lean compiler: {e}");
                return ExitCode::from(2);
            }
        }
    }

    ExitCode::SUCCESS
}
