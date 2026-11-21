use crate::core::{build_dag, ModuleNode};
use comfy_table::{Cell, Color, Table};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn print_ascii_tree(
    curr: &str,
    nodes: &HashMap<String, ModuleNode>,
    seen_hashes: &mut HashSet<u64>,
    prefix: &str,
    is_last: bool,
    depth: usize,
    max_depth: usize,
) {
    let Some(node) = nodes.get(curr) else { return };
    let connector = if depth == 0 {
        ""
    } else if is_last {
        "└── "
    } else {
        "├── "
    };

    let is_new = seen_hashes.insert(node.content_hash);
    let mut tags = Vec::new();
    if !is_new {
        tags.push("dedup");
    }
    if node.has_heq {
        tags.push("HEq");
    }
    if node.has_heartbeat_hack {
        tags.push("maxHeartbeats");
    }

    let badge = if tags.is_empty() {
        String::new()
    } else {
        format!(" [{}]", tags.join(", "))
    };

    println!("{prefix}{connector}{}{badge}", node.name);

    if !is_new || depth >= max_depth {
        return;
    }

    let children: Vec<&String> = node
        .imports
        .iter()
        .filter(|imp| nodes.contains_key(*imp))
        .collect();

    let next_prefix = if depth == 0 {
        String::new()
    } else if is_last {
        format!("{prefix}    ")
    } else {
        format!("{prefix}│   ")
    };

    for (idx, child) in children.iter().enumerate() {
        let last_child = idx + 1 == children.len();
        print_ascii_tree(
            child,
            nodes,
            seen_hashes,
            &next_prefix,
            last_child,
            depth + 1,
            max_depth,
        );
    }
}

pub fn run_graph(
    src_dir: &Path,
    entry: &str,
    export_unique: Option<PathBuf>,
    tree: bool,
    max_depth: usize,
) -> ExitCode {
    let (total_files, nodes) = build_dag(src_dir);

    if !nodes.contains_key(entry) {
        eprintln!("Error: entry module `{entry}` not found in {:?}", src_dir);
        return ExitCode::from(2);
    }

    if tree {
        println!("\nDeduplicated ASCII Dependency Tree (max depth: {max_depth}):");
        let mut tree_seen = HashSet::new();
        print_ascii_tree(entry, &nodes, &mut tree_seen, "", true, 0, max_depth);
    }

    let mut visited = HashSet::new();
    let mut seen_hashes = HashSet::new();
    let mut queue = VecDeque::new();
    let mut unique_paths = Vec::new();

    visited.insert(entry.to_string());
    queue.push_back((entry.to_string(), 0usize));

    let mut depth_stats: HashMap<usize, (usize, usize, usize, usize, usize)> = HashMap::new();
    let mut first_anomaly: Option<(usize, String, &'static str)> = None;

    while let Some((curr, depth)) = queue.pop_front() {
        let Some(node) = nodes.get(&curr) else { continue };
        let stat = depth_stats.entry(depth).or_insert((0, 0, 0, 0, 0));
        stat.0 += 1;

        if seen_hashes.insert(node.content_hash) {
            stat.1 += 1;
            unique_paths.push(node.path.display().to_string());
            if node.has_heq {
                stat.2 += 1;
                if first_anomaly.is_none() {
                    first_anomaly = Some((depth, node.name.clone(), "HEq (heterogeneous equality)"));
                }
            }
            stat.4 += node.axioms_count;
            if node.has_heartbeat_hack {
                stat.3 += 1;
                if first_anomaly.is_none() {
                    first_anomaly = Some((depth, node.name.clone(), "maxHeartbeats override"));
                }
            }
        } else {
            continue;
        }

        for imp in &node.imports {
            if nodes.contains_key(imp) && visited.insert(imp.clone()) {
                queue.push_back((imp.clone(), depth + 1));
            }
        }
    }

    let mut table = Table::new();
    table.set_header(vec![
        "Depth",
        "Reachable",
        "Unique (Deduplicated)",
        "HEq Bridges",
        "Heartbeat Overrides",
        "Custom Axioms",
    ]);

    let mut depths: Vec<usize> = depth_stats.keys().copied().collect();
    depths.sort_unstable();

    let (mut tot_m, mut tot_u, mut tot_h, mut tot_b, mut tot_a) = (0, 0, 0, 0, 0);
    for d in &depths {
        let (m, u, h, b, a) = depth_stats[d];
        tot_m += m;
        tot_u += u;
        tot_h += h;
        tot_b += b;
        tot_a += a;
        table.add_row(vec![
            Cell::new(format!("Level {d}")),
            Cell::new(m),
            Cell::new(u).fg(Color::Cyan),
            Cell::new(h).fg(if h > 0 { Color::Yellow } else { Color::Green }),
            Cell::new(b).fg(if b > 0 { Color::Red } else { Color::Green }),
            Cell::new(a).fg(if a > 0 { Color::Red } else { Color::Green }),
        ]);
    }

    table.add_row(vec![
        Cell::new("TOTAL"),
        Cell::new(tot_m),
        Cell::new(tot_u).fg(Color::Cyan),
        Cell::new(tot_h),
        Cell::new(tot_b),
        Cell::new(tot_a),
    ]);

    println!("\n{table}");
    println!(
        "Total files on disk: {} | Reachable from `{}`: {} | Unique DAG nodes: {} (deduplicated {} clones)",
        total_files,
        entry,
        tot_m,
        tot_u,
        tot_m.saturating_sub(tot_u)
    );

    if let Some((d, name, reason)) = first_anomaly {
        println!("\nFirst structural anomaly at depth {d}: `{name}` ({reason})");
    }

    if let Some(out_file) = export_unique {
        if fs::write(&out_file, unique_paths.join("\n")).is_ok() {
            println!("Exported {} unique module paths to {:?}", unique_paths.len(), out_file);
        }
    }

    ExitCode::SUCCESS
}

pub fn run_check(src_dir: &Path, entry: &str, allow_axioms: bool) -> ExitCode {
    let (total_files, nodes) = build_dag(src_dir);

    if !nodes.contains_key(entry) {
        eprintln!("Error: entry module `{entry}` not found in {:?}", src_dir);
        return ExitCode::from(2);
    }

    let mut visited = HashSet::new();
    let mut seen_hashes = HashSet::new();
    let mut queue = VecDeque::new();

    visited.insert(entry.to_string());
    queue.push_back(entry.to_string());

    let mut tot_sorry = 0usize;
    let mut tot_axioms = 0usize;
    let mut tot_true_stubs = 0usize;
    let mut tot_heartbeats = 0usize;
    let mut tot_clones = 0usize;

    let mut issues_table = Table::new();
    issues_table.set_header(vec!["Module", "sorry/admit", "Axioms", ": True Stubs", "Heartbeat Hack"]);

    while let Some(curr) = queue.pop_front() {
        let Some(node) = nodes.get(&curr) else { continue };

        if !seen_hashes.insert(node.content_hash) {
            tot_clones += 1;
            continue;
        }

        tot_sorry += node.sorry_count;
        tot_axioms += node.axioms_count;
        tot_true_stubs += node.trivial_true_count;
        if node.has_heartbeat_hack {
            tot_heartbeats += 1;
        }

        let has_issue = node.sorry_count > 0
            || (!allow_axioms && node.axioms_count > 0)
            || node.trivial_true_count > 0
            || node.has_heartbeat_hack;

        if has_issue {
            issues_table.add_row(vec![
                Cell::new(&node.name),
                Cell::new(node.sorry_count).fg(if node.sorry_count > 0 { Color::Red } else { Color::Green }),
                Cell::new(node.axioms_count).fg(if node.axioms_count > 0 { Color::Yellow } else { Color::Green }),
                Cell::new(node.trivial_true_count).fg(if node.trivial_true_count > 0 { Color::Red } else { Color::Green }),
                Cell::new(if node.has_heartbeat_hack { "YES" } else { "no" })
                    .fg(if node.has_heartbeat_hack { Color::Red } else { Color::Green }),
            ]);
        }

        for imp in &node.imports {
            if nodes.contains_key(imp) && visited.insert(imp.clone()) {
                queue.push_back(imp.clone());
            }
        }
    }

    println!("\n=== AI-Agent & Formal Proof Integrity Check (`{entry}`) ===");
    println!(
        "Files on disk: {} | Reachable: {} | Clones skipped: {}",
        total_files,
        visited.len(),
        tot_clones
    );
    println!(
        "Summary: sorry/admit = {} | custom axioms = {} | `: True` stubs = {} | heartbeat overrides = {}",
        tot_sorry, tot_axioms, tot_true_stubs, tot_heartbeats
    );

    let failed = tot_sorry > 0
        || (!allow_axioms && tot_axioms > 0)
        || tot_true_stubs > 0
        || tot_heartbeats > 0;

    if failed {
        println!("\nFlagged Modules:\n{issues_table}");
        eprintln!("CHECK FAILED: Unproven gaps, custom axioms, or trivial `: True` stubs detected.");
        ExitCode::from(1)
    } else {
        println!("CHECK PASSED: Proof DAG is clean and self-contained.");
        ExitCode::SUCCESS
    }
}
