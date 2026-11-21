use comfy_table::{Cell, Color, Table};
use rayon::prelude::*;
use regex::Regex;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

struct ModuleNode {
    name: String,
    path: PathBuf,
    imports: Vec<String>,
    content_hash: u64,
    has_heq: bool,
    has_heartbeat_hack: bool,
}

fn normalize_and_hash(text: &str) -> u64 {
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

pub fn run_graph(src_dir: &Path, entry: &str, export_unique: Option<PathBuf>) {
    let imp_re = Regex::new(r"(?m)^import\s+([A-Za-z0-9_.']+)").unwrap();

    let files: Vec<PathBuf> = WalkDir::new(src_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "lean"))
        .map(|e| e.path().to_path_buf())
        .collect();

    let nodes: HashMap<String, ModuleNode> = files
        .par_iter()
        .filter_map(|path| {
            let content = fs::read_to_string(path).ok()?;
            let rel = path.strip_prefix(src_dir).ok()?;
            let mod_name = rel.with_extension("").to_string_lossy().replace('/', ".");
            let imports = imp_re
                .captures_iter(&content)
                .map(|c| c[1].to_string())
                .collect();

            let content_hash = normalize_and_hash(&content);
            let has_heq = content.contains("HEq ");
            let has_heartbeat_hack =
                content.contains("maxHeartbeats 0") || content.contains("maxHeartbeats 4000000");

            Some((
                mod_name.clone(),
                ModuleNode {
                    name: mod_name,
                    path: path.clone(),
                    imports,
                    content_hash,
                    has_heq,
                    has_heartbeat_hack,
                },
            ))
        })
        .collect();

    let mut visited = HashSet::new();
    let mut seen_hashes = HashSet::new();
    let mut queue = VecDeque::new();
    let mut unique_paths = Vec::new();

    if nodes.contains_key(entry) {
        visited.insert(entry.to_string());
        queue.push_back((entry.to_string(), 0usize));
    } else {
        eprintln!("Error: entry module `{entry}` not found in {:?}", src_dir);
        return;
    }

    let mut depth_stats: HashMap<usize, (usize, usize, usize, usize)> = HashMap::new();
    let mut first_anomaly: Option<(usize, String, &'static str)> = None;

    while let Some((curr, depth)) = queue.pop_front() {
        let Some(node) = nodes.get(&curr) else { continue };
        let stat = depth_stats.entry(depth).or_insert((0, 0, 0, 0));
        stat.0 += 1;

        let is_unique = seen_hashes.insert(node.content_hash);
        if is_unique {
            stat.1 += 1;
            unique_paths.push(node.path.display().to_string());
            if node.has_heq {
                stat.2 += 1;
                if first_anomaly.is_none() {
                    first_anomaly = Some((depth, node.name.clone(), "HEq (heterogeneous equality)"));
                }
            }
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
    ]);

    let mut depths: Vec<usize> = depth_stats.keys().copied().collect();
    depths.sort_unstable();

    let (mut tot_m, mut tot_u, mut tot_h, mut tot_b) = (0, 0, 0, 0);
    for d in &depths {
        let (m, u, h, b) = depth_stats[d];
        tot_m += m;
        tot_u += u;
        tot_h += h;
        tot_b += b;
        table.add_row(vec![
            Cell::new(format!("Level {d}")),
            Cell::new(m),
            Cell::new(u).fg(Color::Cyan),
            Cell::new(h).fg(if h > 0 { Color::Yellow } else { Color::Green }),
            Cell::new(b).fg(if b > 0 { Color::Red } else { Color::Green }),
        ]);
    }

    table.add_row(vec![
        Cell::new("TOTAL"),
        Cell::new(tot_m),
        Cell::new(tot_u).fg(Color::Cyan),
        Cell::new(tot_h),
        Cell::new(tot_b),
    ]);

    println!("\n{table}");
    println!(
        "Total files on disk: {} | Reachable from `{}`: {} | Unique DAG nodes: {} (deduplicated {} clones)",
        files.len(),
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
}
