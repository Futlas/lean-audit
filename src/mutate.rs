use crate::core::find_lake_root;
use comfy_table::{Cell, Color, Table};
use rayon::prelude::*;
use regex::Regex;
use serde::Serialize;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use indicatif::{ProgressBar, ProgressStyle};
use std::sync::atomic::{AtomicUsize, Ordering};
use walkdir::WalkDir;

#[derive(Clone, Serialize)]
struct Mutant {
    file_path: PathBuf,
    theorem_name: String,
    category: String,
    kind: String,
    origin: String,
    survived: bool,
}

#[derive(Serialize)]
struct AuditReport {
    scanned_files: usize,
    total_mutants: usize,
    survived_mutants: usize,
    env_errors: usize,
    mutants: Vec<Mutant>,
}

enum Runner<'a> {
    Lake(&'a Path),
    Direct(&'a str, &'a [&'a str]),
}

fn split_top_level_parens(s: &str) -> Vec<(usize, usize)> {
    let mut blocks = Vec::new();
    let (mut dp, mut db, mut dc) = (0usize, 0usize, 0usize);
    let mut start = None;

    for (i, ch) in s.char_indices() {
        match ch {
            '(' => {
                if dp == 0 && db == 0 && dc == 0 {
                    start = Some(i);
                }
                dp += 1;
            }
            ')' => {
                dp = dp.saturating_sub(1);
                if dp == 0 && db == 0 && dc == 0 {
                    if let Some(st) = start.take() {
                        blocks.push((st, i + ch.len_utf8()));
                    }
                }
            }
            '[' => db += 1,
            ']' => db = db.saturating_sub(1),
            '{' => dc += 1,
            '}' => dc = dc.saturating_sub(1),
            _ => {}
        }
    }
    blocks
}

fn parse_signature(rest: &str) -> Option<(&str, &str, usize)> {
    let (mut dp, mut db, mut dc) = (0usize, 0usize, 0usize);
    let mut colon_pos = None;
    let bytes = rest.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        let ch = rest[i..].chars().next()?;
        match ch {
            '(' => dp += 1,
            ')' => dp = dp.saturating_sub(1),
            '[' => db += 1,
            ']' => db = db.saturating_sub(1),
            '{' => dc += 1,
            '}' => dc = dc.saturating_sub(1),
            '\n' if dp == 0 && db == 0 && dc == 0 => {
                let next_line = &rest[i + 1..];
                if next_line.starts_with("theorem ")
                    || next_line.starts_with("lemma ")
                    || next_line.starts_with("def ")
                    || next_line.starts_with("structure ")
                {
                    return None;
                }
            }
            ':' if dp == 0 && db == 0 && dc == 0 => {
                if rest[i..].starts_with(":=") {
                    let after_assign = rest[i + 2..].trim_start();
                    if after_assign.starts_with("by") {
                        let by_offset = rest.len() - after_assign.len() + 2;
                        let c_pos = colon_pos?;
                        return Some((&rest[..c_pos], rest[c_pos + 1..i].trim(), by_offset));
                    }
                    return None;
                } else if colon_pos.is_none() {
                    colon_pos = Some(i);
                }
            }
            _ => {}
        }
        i += ch.len_utf8();
    }
    None
}

fn is_likely_data_binder(block: &str, rest_of_sig: &str) -> bool {
    let inner = block.trim_start_matches('(').trim_end_matches(')');
    let Some((lhs, _)) = inner.split_once(':') else { return true };
    let var_names: Vec<&str> = lhs.split_whitespace().collect();
    if var_names.is_empty() {
        return true;
    }
    var_names.iter().any(|v| {
        v.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
            && rest_of_sig.contains(v)
    })
}

fn check_lean_file(runner: &Runner, path: &Path) -> Result<bool, ()> {
    let output = match runner {
        Runner::Lake(root) => Command::new("lake")
            .args(["env", "lean"])
            .arg(path)
            .current_dir(root)
            .output(),
        Runner::Direct(bin, args) => Command::new(bin).args(*args).arg(path).output(),
    };

    match output {
        Ok(out) => {
            let stderr = String::from_utf8_lossy(&out.stderr);
            if stderr.contains("unknown module prefix")
                || stderr.contains("unknown identifier")
                || stderr.contains("unknown constant")
                || out.status.code().is_none()
            {
                Err(())
            } else {
                Ok(out.status.success() && !stderr.contains("sorry"))
            }
        }
        Err(_) => Err(()),
    }
}

pub fn run_mutate(
    path: &Path,
    out_dir: &Path,
    filter: Option<String>,
    run: bool,
    strip_imports: bool,
    verify_orig: bool,
    use_lake: bool,
    vacuous_only: bool,
    limit: Option<usize>,
    lean_cmd: &str,
) -> ExitCode {
    let lake_root = if use_lake {
        match find_lake_root(path) {
            Some(r) => {
                println!("Detected Lake workspace root: {:?}", r);
                Some(r)
            }
            None => {
                eprintln!("Error: --lake specified, but no lakefile.lean or lakefile.toml found above {:?}", path);
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };

    let _ = fs::remove_dir_all(out_dir);
    fs::create_dir_all(out_dir).expect("Failed to create output directory");

    let decl_re = Regex::new(r"(?m)^(theorem|lemma)\s+([A-Za-z0-9_.']+)").unwrap();
    let filter_lower = filter.as_ref().map(|f| f.to_lowercase());

    let cmd_parts: Vec<&str> = lean_cmd.split_whitespace().collect();
    let bin = cmd_parts.first().copied().unwrap_or("lean");
    let empty_args: Vec<&str> = Vec::new();
    let args = if cmd_parts.len() > 1 { &cmd_parts[1..] } else { &empty_args[..] };

    let runner = match &lake_root {
        Some(root) => Runner::Lake(root.as_path()),
        None => Runner::Direct(bin, args),
    };

    let files: Vec<PathBuf> = if path.is_file() && path.extension().is_some_and(|e| e == "txt") {
        fs::read_to_string(path)
            .unwrap_or_default()
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(PathBuf::from)
            .collect()
    } else {
        WalkDir::new(path)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().is_some_and(|ext| ext == "lean"))
            .map(|e| e.path().to_path_buf())
            .collect()
    };

    let skipped_orig = AtomicUsize::new(0);

    let mut mutants: Vec<Mutant> = files
        .par_iter()
        .flat_map(|file| {
            let Ok(raw_content) = fs::read_to_string(file) else { return Vec::new() };
            let content = if strip_imports {
                raw_content
                    .lines()
                    .filter(|l| !l.trim_start().starts_with("import "))
                    .collect::<Vec<_>>()
                    .join("\n")
            } else {
                raw_content
            };

            if verify_orig {
                let tmp_orig = out_dir.join(format!(
                    "_orig_{}_{}",
                    rayon::current_thread_index().unwrap_or(0),
                    file.file_name().unwrap_or_default().to_string_lossy()
                ));
                if fs::write(&tmp_orig, &content).is_ok() {
                    let ok = check_lean_file(&runner, &tmp_orig).unwrap_or(false);
                    let _ = fs::remove_file(&tmp_orig);
                    if !ok {
                        skipped_orig.fetch_add(1, Ordering::Relaxed);
                        return Vec::new();
                    }
                }
            }

            let mut local_mutants = Vec::new();

            for (idx, cap) in decl_re.captures_iter(&content).enumerate() {
                let m0 = cap.get(0).unwrap();
                let kind = cap.get(1).unwrap().as_str();
                let name = cap.get(2).unwrap().as_str();

                if let Some(ref flt) = filter_lower {
                    if !name.to_lowercase().contains(flt) {
                        continue;
                    }
                }

                let rest = &content[m0.end()..];
                let Some((hyps, target, by_end)) = parse_signature(rest) else { continue };
                let prefix = &content[..m0.start()];
                let suffix = &content[m0.end() + by_end..];
                let safe_name = name.replace('.', "_");
                let origin = format!("{}:{}", file.display(), name);

                let false_code = format!(
                    "{prefix}{kind} {name}_MUTANT_FALSE{hyps}: False := by\n  first | omega | contradiction | decide | simp\n"
                );
                let out_false = out_dir.join(format!("{safe_name}_{idx}_false.lean"));
                if fs::write(&out_false, false_code).is_ok() {
        
            let stub_re = Regex::new(r"(∧\s*True\b|/\\\s*True\b|:\s*True\b)").unwrap();
            let file_stem = file.file_stem().unwrap_or_default().to_string_lossy().replace('.', "_");
            for (s_idx, m) in stub_re.find_iter(&content).enumerate() {
                let mut mutated = content.clone();
                let replacement = m.as_str().replace("True", "False");
                mutated.replace_range(m.range(), &replacement);
                let line_num = content[..m.start()].matches('\n').count() + 1;
                let out_stub = out_dir.join(format!("{file_stem}_stub_{s_idx}_{line_num}.lean"));
                if fs::write(&out_stub, mutated).is_ok() {
                    local_mutants.push(Mutant {
                        file_path: out_stub,
                        theorem_name: format!("line_{line_num}"),
                        category: "STUB_INJECTION".into(),
                        kind: "True -> False".into(),
                        origin: format!("{}:line_{line_num}", file.display()),
                        survived: false,
                    });
                }
            }

            local_mutants.push(Mutant {
                        file_path: out_false,
                        theorem_name: name.to_string(),
                        category: "VACUOUS_TRUTH".into(),
                        kind: "Target -> False".into(),
                        origin: origin.clone(),
                        survived: false,
                    });
                }

                if !vacuous_only {
                for (h_idx, (st, en)) in split_top_level_parens(hyps).iter().enumerate() {
                    let removed = &hyps[*st..*en];
                    if !removed.contains(':') {
                        continue;
                    }
                    let rest_sig = format!("{}{}", &hyps[*en..], target);
                    if is_likely_data_binder(removed, &rest_sig) {
                        continue;
                    }

                    let mut new_hyps = String::new();
                    new_hyps.push_str(&hyps[..*st]);
                    new_hyps.push_str(&hyps[*en..]);

                    let drop_code = format!("{prefix}{kind} {name}_DROP_H{h_idx}{new_hyps}: {target} := by{suffix}");
                    let out_drop = out_dir.join(format!("{safe_name}_{idx}_drop{h_idx}.lean"));
                    if fs::write(&out_drop, drop_code).is_ok() {
                        local_mutants.push(Mutant {
                            file_path: out_drop,
                            theorem_name: name.to_string(),
                            category: "UNUSED_HYP".into(),
                            kind: format!("Drop {}", removed.trim()),
                            origin: origin.clone(),
                            survived: false,
                        });
                    }
                }

                let replacements = [("<", "≤"), ("=", "≠"), ("1 / 2", "1 / 4")];
                for (r_idx, (from, to)) in replacements.iter().enumerate() {
                    if target.contains(from) && !target.contains(":=") {
                        let mut_target = target.replacen(from, to, 1);
                        let op_code = format!("{prefix}{kind} {name}_OP{r_idx}{hyps}: {mut_target} := by{suffix}");
                        let out_op = out_dir.join(format!("{safe_name}_{idx}_op{r_idx}.lean"));
                        if fs::write(&out_op, op_code).is_ok() {
                            local_mutants.push(Mutant {
                                file_path: out_op,
                                theorem_name: name.to_string(),
                                category: "BOUNDARY_SHIFT".into(),
                                kind: format!("'{from}' -> '{to}'"),
                                origin: origin.clone(),
                                survived: false,
                            });
                        }
                    }
                }
                }
            }
            local_mutants
        })
        .collect();

    if let Some(max_m) = limit {
        if mutants.len() > max_m {
            mutants.truncate(max_m);
        }
    }

    let survived_count = AtomicUsize::new(0);
    let env_errors = AtomicUsize::new(0);

    if run {
        let label = if use_lake { "lake env lean" } else { lean_cmd };
        println!("Running parallel verification of {} mutants via `{label}`...", mutants.len());
        let pb = ProgressBar::new(mutants.len() as u64);
        pb.set_style(
            ProgressStyle::default_bar()
                .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta}) | {msg}")
                .unwrap()
                .progress_chars("█▓░"),
        );
        mutants.par_iter_mut().for_each(|m| {
            match check_lean_file(&runner, &m.file_path) {
                Ok(true) => {
                    m.survived = true;
                    let s = survived_count.fetch_add(1, Ordering::Relaxed) + 1;
                    pb.set_message(format!("survivors: {s}"));
                }
                Ok(false) => {}
                Err(()) => {
                    env_errors.fetch_add(1, Ordering::Relaxed);
                }
            }
            pb.inc(1);
        });
        pb.finish_with_message(format!("done (survivors: {})", survived_count.load(Ordering::Relaxed)));
    }

    let mut cnt_vac = (0usize, 0usize);
    let mut cnt_stub = (0usize, 0usize);
    let mut cnt_hyp = (0usize, 0usize);
    let mut cnt_bnd = (0usize, 0usize);

    for m in &mutants {
        let pair = match m.category.as_str() {
            "STUB_INJECTION" => &mut cnt_stub,
            "VACUOUS_TRUTH" => &mut cnt_vac,
            "UNUSED_HYP" => &mut cnt_hyp,
            _ => &mut cnt_bnd,
        };
        pair.0 += 1;
        if m.survived {
            pair.1 += 1;
        }
    }

    let mut summary = Table::new();
    summary.set_header(vec!["Mutation Category", "Generated", "Survived (Suspicious)"]);
    summary.add_row(vec![
        Cell::new("STUB_INJECTION (True -> False)"),
        Cell::new(cnt_stub.0),
        Cell::new(cnt_stub.1).fg(if cnt_stub.1 > 0 { Color::Red } else { Color::Green }),
    ]);
    summary.add_row(vec![
        Cell::new("VACUOUS_TRUTH (Target -> False)"),
        Cell::new(cnt_vac.0),
        Cell::new(cnt_vac.1).fg(if cnt_vac.1 > 0 { Color::Red } else { Color::Green }),
    ]);
    summary.add_row(vec![
        Cell::new("UNUSED_HYP (Hypothesis Removal)"),
        Cell::new(cnt_hyp.0),
        Cell::new(cnt_hyp.1).fg(if cnt_hyp.1 > 0 { Color::Yellow } else { Color::Green }),
    ]);
    summary.add_row(vec![
        Cell::new("BOUNDARY_SHIFT (Operator/Constant)"),
        Cell::new(cnt_bnd.0),
        Cell::new(cnt_bnd.1).fg(if cnt_bnd.1 > 0 { Color::Red } else { Color::Green }),
    ]);
    summary.add_row(vec![
        Cell::new(format!("TOTAL (Files scanned: {})", files.len())),
        Cell::new(mutants.len()),
        Cell::new(survived_count.load(Ordering::Relaxed)),
    ]);

    println!("\n{summary}");

    let skipped = skipped_orig.load(Ordering::Relaxed);
    if skipped > 0 {
        println!("Skipped uncompilable original files (--verify-orig): {skipped}");
    }

    let errs = env_errors.load(Ordering::Relaxed);
    if errs > 0 {
        println!("Environment / missing dependency errors during mutant checks: {errs}");
    }

    let final_survived = survived_count.load(Ordering::Relaxed);
    if run && final_survived > 0 {
        let mut surv_table = Table::new();
        surv_table.set_header(vec!["Category", "Mutation", "Origin"]);
        for m in mutants.iter().filter(|m| m.survived) {
            surv_table.add_row(vec![
                Cell::new(&m.category).fg(Color::Red),
                Cell::new(&m.kind),
                Cell::new(&m.origin),
            ]);
        }
        println!("\nSURVIVING MUTANTS DETECTED:\n{surv_table}");
    }

    let report = AuditReport {
        scanned_files: files.len(),
        total_mutants: mutants.len(),
        survived_mutants: final_survived,
        env_errors: errs,
        mutants,
    };

    let report_path = out_dir.join("report.json");
    if let Ok(json) = serde_json::to_string_pretty(&report) {
        let _ = fs::write(&report_path, json);
    }
    println!("JSON report saved to: {:?}\n", report_path);

    if run && final_survived > 0 {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
