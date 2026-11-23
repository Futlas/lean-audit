use crate::core::{strip_lean_comments, ProofDag};
use comfy_table::{presets::UTF8_HORIZONTAL_ONLY, Cell, Color, ContentArrangement, Table};
use rayon::prelude::*;
use regex::Regex;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub struct NodeFeatures {
    pub module: String,
    pub depth: usize,
    pub in_degree: usize,
    pub out_degree: usize,
    pub lines: usize,
    pub decls: usize,
    pub true_stubs: usize,
    pub sorry_count: usize,
    pub axioms_count: usize,
    pub has_heq: usize,
    pub has_heartbeat: usize,
    pub tactic_score: usize,
    pub risk_score: f64,
}

/// Ансамбль градиентного бустинга из 6 решающих пней (GBDT) + сигмоида для точного ранжирования (0.0..100.0)
fn gbdt_risk_score(
    depth: usize,
    in_degree: usize,
    decls: usize,
    true_stubs: usize,
    sorry_count: usize,
    axioms_count: usize,
    has_heq: usize,
    has_heartbeat: usize,
    tactic_score: usize,
) -> f64 {
    if sorry_count > 0 || axioms_count > 0 {
        return 100.0;
    }
    // Базовый априорный логит (низкий фон риска)
    let mut logit: f64 = -3.2;

    // Пень 1: Наличие и количество заглушек `: True` / `∧ True`
    if true_stubs > 0 {
        logit += 2.8 + 0.65 * (true_stubs as f64).ln_1p();
    }
    // Пень 2: Несущая способность узла (сколько других модулей опираются на него)
    if in_degree > 0 {
        logit += 0.48 * (in_degree as f64).ln_1p();
    }
    // Пень 3: Близость к корневой теореме Main.lean (чем меньше depth, тем опаснее подмена)
    logit += 1.6 / (1.0 + (depth as f64) * 0.25);

    // Пень 4: Аномалия "пустого интерфейса" (много деклараций при полном отсутствии тактик)
    if decls >= 3 && tactic_score == 0 {
        logit += 1.15;
    } else if decls > 0 {
        let tac_density = (tactic_score as f64) / (decls as f64);
        if tac_density < 0.2 {
            logit += 0.45;
        }
    }

    // Пень 5 и 6: Гетерогенные равенства HEq и отключение таймаута maxHeartbeats
    if has_heq > 0 {
        logit += 0.75;
    }
    if has_heartbeat > 0 {
        logit += 0.85;
    }

    let prob = 1.0 / (1.0 + (-logit).exp());
    (prob * 1000.0).round() / 10.0
}

pub fn run_rank(src_dir: &Path, entry: &str, top_n: usize, min_depth: usize, max_depth: Option<usize>, min_risk: f64, inspect_n: usize, ctx_lines: usize, export_paths: Option<PathBuf>, csv_out: Option<PathBuf>) -> ExitCode {
    let dag = match ProofDag::build(src_dir, entry, max_depth) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Error: {e}");
            return ExitCode::from(2);
        }
    };

    let mut depth_map: HashMap<String, usize> = HashMap::new();
    let mut in_deg: HashMap<String, usize> = HashMap::new();
    let mut reachable_list: Vec<String> = Vec::new();

    for (d, layer) in dag.layers.iter().enumerate() {
        for mod_name in layer {
            depth_map.insert(mod_name.clone(), d);
            if d >= min_depth && max_depth.map(|mx| d <= mx).unwrap_or(true) { reachable_list.push(mod_name.clone()); }
            if let Some(node) = dag.nodes.get(mod_name) {
                for imp in &node.imports {
                    if dag.nodes.contains_key(imp) {
                        *in_deg.entry(imp.clone()).or_insert(0) += 1;
                    }
                }
            }
        }
    }

    let decl_re = Regex::new(r"(?m)^(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|structure|inductive)\s+").unwrap();
    let tac_re = Regex::new(r"\b(simp|omega|linarith|ring|aesop|decide|norm_num|exact|apply|induction|by_contra|have)\b").unwrap();

    let mut features: Vec<NodeFeatures> = reachable_list
        .par_iter()
        .filter_map(|mod_name| {
            let node = dag.nodes.get(mod_name)?;
            let raw = fs::read_to_string(&node.path).ok()?;
            let clean = strip_lean_comments(&raw);
            let lines = raw.lines().count();
            let decls = decl_re.find_iter(&clean).count();
            let tactic_score = tac_re.find_iter(&clean).count();
            let depth = *depth_map.get(mod_name).unwrap_or(&0);
            let in_degree = *in_deg.get(mod_name).unwrap_or(&0);
            let out_degree = node.imports.len();
            let has_heq = usize::from(node.has_heq);
            let has_heartbeat = usize::from(node.has_heartbeat_hack);
            let risk_score = gbdt_risk_score(
                depth, in_degree, decls, node.trivial_true_count,
                node.sorry_count, node.axioms_count, has_heq, has_heartbeat, tactic_score,
            );
            Some(NodeFeatures {
                module: mod_name.clone(), depth, in_degree, out_degree, lines, decls,
                true_stubs: node.trivial_true_count, sorry_count: node.sorry_count,
                axioms_count: node.axioms_count, has_heq, has_heartbeat, tactic_score, risk_score,
            })
        })
        .collect();

    if let Some(md) = max_depth {
        features.retain(|f| f.depth <= md);
    }
    features.retain(|f| f.risk_score >= min_risk);
    features.sort_by(|a, b| b.risk_score.total_cmp(&a.risk_score).then_with(|| b.in_degree.cmp(&a.in_degree)));

    if let Some(ref exp_p) = export_paths {
        let paths: Vec<String> = features.iter().take(top_n)
            .filter_map(|f| dag.nodes.get(&f.module).map(|n| n.path.to_string_lossy().to_string()))
            .collect();
        let _ = fs::write(exp_p, paths.join("\n"));
        println!("Exported {} targeted module paths (top {}, max_depth={:?}, min_risk={:.1}%) to: {:?}", paths.len(), top_n, max_depth, min_risk, exp_p);
    }

    if let Some(ref csv_path) = csv_out {
        let mut csv = String::from("module,depth,in_degree,out_degree,lines,decls,true_stubs,sorry_count,axioms_count,has_heq,has_heartbeat,tactic_score,risk_score\n");
        for f in &features {
            csv.push_str(&format!(
                "{},{},{},{},{},{},{},{},{},{},{},{},{}\n",
                f.module, f.depth, f.in_degree, f.out_degree, f.lines, f.decls,
                f.true_stubs, f.sorry_count, f.axioms_count, f.has_heq, f.has_heartbeat,
                f.tactic_score, f.risk_score
            ));
        }
        let _ = fs::write(csv_path, csv);
        println!("Exported {} node feature vectors to: {:?}", features.len(), csv_path);
    }

    let mut table = Table::new();
    table.load_preset(UTF8_HORIZONTAL_ONLY);
    table.set_content_arrangement(ContentArrangement::Dynamic);
    table.set_header(vec!["Risk", "Depth", "In-Deg", "Decls", ": True", "HEq", "HB", "Tactics", "Module"]);
    for f in features.iter().take(top_n) {
        let c = if f.risk_score >= 80.0 { Color::Red } else if f.risk_score >= 45.0 { Color::Yellow } else { Color::Green };
        table.add_row(vec![
            Cell::new(format!("{:.1}%", f.risk_score)).fg(c),
            Cell::new(f.depth), Cell::new(f.in_degree), Cell::new(f.decls),
            Cell::new(f.true_stubs), Cell::new(f.has_heq), Cell::new(f.has_heartbeat),
            Cell::new(f.tactic_score), Cell::new(if f.module.len() > 62 { format!("…{}", &f.module[f.module.len()-61..]) } else { f.module.clone() }),
        ]);
    }
    println!("\n=== Decision-Tree Anomaly & Load-Bearing Node Ranking (Top {top_n}) ===");
    println!("{table}");

    if inspect_n > 0 {
        let stub_re = Regex::new(r"(?m)^[^|\n]*(?::\s*True\b|∧\s*True\b|/\\\s*True\b|\bTrue\s*(?:∧|/\\)|(?:→|->)\s*True\b)").unwrap();
        println!("\n=== Code Context Inspection (Top {inspect_n} Suspects, ±{ctx_lines} lines) ===");
        for (idx, f) in features.iter().take(inspect_n).enumerate() {
            let Some(node) = dag.nodes.get(&f.module) else { continue };
            let Ok(raw) = fs::read_to_string(&node.path) else { continue };
            let lines: Vec<&str> = raw.lines().collect();
            println!("\n--- [#{}] {} (Risk: {:.1}%, Depth: {}, In-Deg: {}) ---", idx + 1, f.module, f.risk_score, f.depth, f.in_degree);
            println!("File: {}", node.path.display());
            let mut shown = 0usize;
            for (l_idx, line) in lines.iter().enumerate() {
                if !line.trim_start().starts_with("--") && stub_re.is_match(line) {
                    let start = l_idx.saturating_sub(ctx_lines);
                    let end = (l_idx + ctx_lines + 1).min(lines.len());
                    for j in start..end {
                        let mark = if j == l_idx { ">>>" } else { "   " };
                        println!("  {mark} {:4} | {}", j + 1, lines[j]);
                    }
                    shown += 1;
                    if shown >= 2 { break; }
                }
            }
            if shown == 0 {
                for j in 0..lines.len().min(ctx_lines * 2 + 1) {
                    println!("       {:4} | {}", j + 1, lines[j]);
                }
            }
        }
    }

    ExitCode::SUCCESS
}
