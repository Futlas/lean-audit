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
    let imp_re = Regex::new(r"(?m)^import\s+([A-Za-z0-9_.']+)").unwrap();

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
                .filter_map(|c| c.get(1).map(|m| m.as_str().to_string()))
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
