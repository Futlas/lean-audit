use crate::core::ProofDag;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

pub fn run_resume(
    src_dir: &Path,
    entry: &str,
    target: Option<String>,
    max_layers: usize,
    md_out: Option<PathBuf>,
    tex_out: Option<PathBuf>,
) -> ExitCode {
    let t0 = Instant::now();
    println!("=========================================================================");
    println!("  LEAN-AUDIT FULL INTEGRITY & ARCHITECTURE RESUME (`{entry}`)");
    println!("=========================================================================");

    // 1. Графовый и статический аудит
    let dag = match ProofDag::build(src_dir, entry, None) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Error building DAG: {e}");
            return ExitCode::from(2);
        }
    };

    let mut total_sorry = 0usize;
    let mut total_axioms = 0usize;
    let mut total_true_stubs = 0usize;
    let mut flagged_true_mods = 0usize;
    let mut total_heartbeats = 0usize;
    let mut total_heq = 0usize;

    for layer in &dag.layers {
        for m in layer {
            if let Some(n) = dag.nodes.get(m) {
                total_sorry += n.sorry_count;
                total_axioms += n.axioms_count;
                total_true_stubs += n.trivial_true_count;
                if n.trivial_true_count > 0 { flagged_true_mods += 1; }
                if n.has_heartbeat_hack { total_heartbeats += 1; }
                if n.has_heq { total_heq += 1; }
            }
        }
    }

    println!("\n[1/4] Static & DAG Integrity Scan:");
    println!(
        "  Files on disk: {} | Reachable unique: {} | Clones skipped: {} | Max DAG depth: {}",
        dag.total_files_on_disk,
        dag.nodes.len(),
        dag.clones_skipped,
        dag.layers.len().saturating_sub(1)
    );
    println!(
        "  sorry/admit: {} | custom axioms: {} | `: True` / `∧ True` / `→ True` stubs: {} (in {} modules)",
        total_sorry, total_axioms, total_true_stubs, flagged_true_mods
    );
    println!(
        "  maxHeartbeats overrides: {} | HEq heterogeneous bridges: {}",
        total_heartbeats, total_heq
    );

    // 2. GBDT-скоринг топ-10 модулей
    println!("\n[2/4] GBDT Anomaly & Load-Bearing Node Ranking (Top 10):");
    let _ = crate::rank::run_rank(src_dir, entry, 10, 0, Some(max_layers), 0.0, 5, 3, None, None);

    // 3. Послойное распрямление + прямые трассы до заглушек
    println!("\n[3/4] Layered Proof Flattening & Stub Call-Chain Trace (0..={max_layers}):");
    let targets = target.into_iter().collect();
    let layers_out = PathBuf::from("/tmp/laud_resume_layers");
    let _ = crate::flatten::run_flatten(src_dir, entry, targets, Some(max_layers), md_out.clone(), &layers_out);

    // 4. Генерация чистого LaTeX Blueprint прямо поверх плоских слоёв `Layer_00`..`Layer_05`
    if let Some(ref tex_path) = tex_out {
        println!("\n[4/4] Generating Clean arXiv LaTeX Blueprint from Flattened Layers (`Layer_00` .. `Layer_05`):");
        let bp_depth = max_layers.min(5);
        let _ = crate::blueprint::run_blueprint(&layers_out, "Layer_00", bp_depth, false, false, tex_path.clone(), None, false);
    }

    if let Some(ref report_path) = md_out {
        if let Ok(mut existing) = fs::read_to_string(report_path) {
            let header = format!(
                "# Full Audit Resume: `{}`\n\n- **Files on disk / Reachable:** {} / {}\n- **sorry / custom axioms:** {} / {}\n- **Trivial `True` stubs:** {} (across {} modules)\n- **Heartbeat overrides / HEq modules:** {} / {}\n\n",
                entry, dag.total_files_on_disk, dag.nodes.len(), total_sorry, total_axioms,
                total_true_stubs, flagged_true_mods, total_heartbeats, total_heq
            );
            existing = header + &existing;
            let _ = fs::write(report_path, existing);
        }
    }

    println!("\n=========================================================================");
    println!("  FULL RESUME COMPLETED in {:.2}s", t0.elapsed().as_secs_f64());
    println!("=========================================================================");

    if total_sorry > 0 || total_axioms > 0 || total_true_stubs > 0 {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
