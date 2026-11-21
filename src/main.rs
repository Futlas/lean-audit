mod blueprint;
mod core;
mod graph;
mod mutate;

use clap::{Parser, Subcommand};
use std::path::PathBuf;
use std::process::ExitCode;

#[derive(Parser)]
#[command(
    name = "lean-audit",
    version,
    about = "Fast DAG deduplicator, arXiv-style LaTeX proof outline generator, and mutation auditor for Lean 4"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Analyze import DAG, deduplicate cloned modules, and render ASCII dependency tree
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
        /// Render deduplicated dependency tree in ASCII format
        #[arg(short, long)]
        tree: bool,
        /// Maximum depth for ASCII tree rendering
        #[arg(long, default_value_t = 4)]
        max_depth: usize,
    },
    /// Generate and run proof mutations (vacuous truth, unused hypotheses, boundary shifts)
    Mutate {
        /// Target file or directory
        path: PathBuf,
        /// Output directory for mutants and JSON report
        #[arg(short, long, default_value = "/tmp/lean_mutants")]
        out: PathBuf,
        /// Case-insensitive theorem name filter
        #[arg(short, long)]
        filter: Option<String>,
        /// Execute Lean compiler against generated mutants (exits with code 1 if survivors found)
        #[arg(short, long)]
        run: bool,
        /// Strip `import` lines for standalone core-only execution without Mathlib
        #[arg(long)]
        strip_imports: bool,
        /// Verify that the original file compiles before testing its mutants
        #[arg(long)]
        verify_orig: bool,
        /// Auto-detect Lake workspace root and run via `lake env lean`
        #[arg(long)]
        lake: bool,
        /// Lean compiler command (used when --lake is not set)
        #[arg(long, default_value = "lean")]
        lean_cmd: String,
    },
    /// Export an arXiv-style LaTeX (.tex) and optional Markdown proof outline
    Blueprint {
        /// Root source directory containing .lean files
        #[arg(default_value = "src")]
        src: PathBuf,
        /// Entry module name (without .lean)
        #[arg(short, long, default_value = "Main")]
        entry: String,
        /// Maximum dependency depth to include
        #[arg(long, default_value_t = 4)]
        max_depth: usize,
        /// Include only theorem and lemma declarations (skip def/structure)
        #[arg(long)]
        only_theorems: bool,
        /// Include bare `def ... : Prop` declarations without docstrings
        #[arg(long)]
        include_props: bool,
        /// Output path for LaTeX (.tex) document
        #[arg(short, long, default_value = "proof_outline.tex")]
        tex: PathBuf,
        /// Optional output path for Markdown outline
        #[arg(long)]
        md: Option<PathBuf>,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Commands::Graph {
            src,
            entry,
            export_unique,
            tree,
            max_depth,
        } => graph::run_graph(&src, &entry, export_unique, tree, max_depth),
        Commands::Mutate {
            path,
            out,
            filter,
            run,
            strip_imports,
            verify_orig,
            lake,
            lean_cmd,
        } => mutate::run_mutate(
            &path,
            &out,
            filter,
            run,
            strip_imports,
            verify_orig,
            lake,
            &lean_cmd,
        ),
        Commands::Blueprint {
            src,
            entry,
            max_depth,
            only_theorems,
            include_props,
            tex,
            md,
        } => blueprint::run_blueprint(
            &src,
            &entry,
            max_depth,
            only_theorems,
            include_props,
            tex,
            md,
        ),
    }
}
