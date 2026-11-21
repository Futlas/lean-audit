mod graph;
mod mutate;

use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "lean-audit",
    version,
    about = "Fast DAG deduplicator and proof mutation auditor for Lean 4"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Analyze import DAG, deduplicate cloned modules, and detect structural anomalies by depth
    Graph {
        /// Root source directory containing .lean files
        #[arg(default_value = "src")]
        src: PathBuf,
        /// Entry module name (without .lean)
        #[arg(short, long, default_value = "Main")]
        entry: String,
        /// Optional path to export unique reachable file paths
        #[arg(short, long)]
        export_unique: Option<PathBuf>,
    },
    /// Generate and optionally run proof mutations (vacuous truth, unused hypotheses, boundary shifts)
    Mutate {
        /// Target file or directory
        path: PathBuf,
        /// Output directory for mutants and JSON report
        #[arg(short, long, default_value = "/tmp/lean_mutants")]
        out: PathBuf,
        /// Case-insensitive theorem name filter
        #[arg(short, long)]
        filter: Option<String>,
        /// Execute Lean compiler against generated mutants
        #[arg(short, long)]
        run: bool,
        /// Strip `import` lines for standalone core-only execution without Mathlib
        #[arg(long)]
        strip_imports: bool,
        /// Verify that the original file compiles before testing its mutants
        #[arg(long)]
        verify_orig: bool,
        /// Lean compiler command
        #[arg(long, default_value = "lean")]
        lean_cmd: String,
    },
}

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Commands::Graph {
            src,
            entry,
            export_unique,
        } => graph::run_graph(&src, &entry, export_unique),
        Commands::Mutate {
            path,
            out,
            filter,
            run,
            strip_imports,
            verify_orig,
            lean_cmd,
        } => mutate::run_mutate(&path, &out, filter, run, strip_imports, verify_orig, &lean_cmd),
    }
}
