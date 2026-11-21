mod blueprint;
mod core;
mod graph;
mod mutate;
mod slice;

use clap::{Parser, Subcommand};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(Parser)]
#[command(
    name = "lean-audit",
    version,
    about = "Fast DAG deduplicator, AI-agent proof verifier, LaTeX outline generator, and mutation auditor for Lean 4"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Analyze import DAG, deduplicate cloned modules, and render ASCII dependency tree
    Graph {
        #[arg(default_value = "src")]
        src: PathBuf,
        #[arg(short, long, default_value = "Main")]
        entry: String,
        #[arg(short, long)]
        export_unique: Option<PathBuf>,
        #[arg(short, long)]
        tree: bool,
        #[arg(long, default_value_t = 4)]
        max_depth: usize,
    },
    /// Strict CI and AI-agent integrity check (exits with code 1 on sorry, custom axioms, or `: True` stubs)
    Check {
        #[arg(default_value = "src")]
        src: PathBuf,
        #[arg(short, long, default_value = "Main")]
        entry: String,
        #[arg(long)]
        allow_axioms: bool,
        /// Filter flagged modules by anomaly type: sorry, axioms, true, heartbeat
        #[arg(short, long)]
        filter: Option<String>,
        /// Export paths of flagged modules to a text file for targeted `laud mutate`
        #[arg(short, long)]
        export_flagged: Option<PathBuf>,
    },
    /// Generate AGENTS.md (and optional CLAUDE.md) guardrails for AI coding agents
    InitAgent {
        #[arg(default_value = ".")]
        dir: PathBuf,
        #[arg(long)]
        claude: bool,
    },
    /// Generate and run proof mutations (vacuous truth, unused hypotheses, boundary shifts)
    Mutate {
        path: PathBuf,
        #[arg(short, long, default_value = "/tmp/lean_mutants")]
        out: PathBuf,
        #[arg(short, long)]
        filter: Option<String>,
        #[arg(short, long)]
        run: bool,
        #[arg(long)]
        strip_imports: bool,
        #[arg(long)]
        verify_orig: bool,
        #[arg(long)]
        lake: bool,
        #[arg(long)]
        vacuous_only: bool,
        #[arg(long)]
        limit: Option<usize>,
        #[arg(long, default_value = "lean")]
        lean_cmd: String,
    },
    /// Slice top N levels of the proof pyramid for fast partial compilation & `#print axioms`
    Slice {
        #[arg(default_value = "src")]
        src: PathBuf,
        #[arg(short, long, default_value = "Main")]
        entry: String,
        #[arg(long, default_value_t = 4)]
        max_depth: usize,
        #[arg(short, long, default_value = "/tmp/lean_slice")]
        out: PathBuf,
        /// Theorem names to inspect via `#print axioms` in AuditVerify.lean
        #[arg(long)]
        axioms: Vec<String>,
        /// Prune unused declarations inside modules via top-down symbol reachability
        #[arg(long)]
        tree_shake: bool,
        /// Immediately run `lake env lean` / `lean` on the generated slice
        #[arg(short, long)]
        run: bool,
    },
    /// Export an arXiv-style LaTeX (.tex) and optional Markdown proof outline
    Blueprint {
        #[arg(default_value = "src")]
        src: PathBuf,
        #[arg(short, long, default_value = "Main")]
        entry: String,
        #[arg(long, default_value_t = 4)]
        max_depth: usize,
        #[arg(long)]
        only_theorems: bool,
        #[arg(long)]
        include_props: bool,
        #[arg(short, long, default_value = "proof_outline.tex")]
        tex: PathBuf,
        #[arg(long)]
        md: Option<PathBuf>,
        /// Keep only declarations transitively referenced from the entry module
        #[arg(long)]
        tree_shake: bool,
    },
}

fn write_agent_instructions(dir: &Path, also_claude: bool) -> ExitCode {
    let policy = r#"# Lean 4 Formalization Guardrails (`lean-audit`)

Before marking any Lean 4 task or Pull Request as complete, you MUST follow these rules:

1. **Zero Proof Placeholders:** Never leave `sorry` or `admit` in any reachable module.
2. **No Invented Axioms:** Do not introduce custom `axiom` declarations to bypass hard lemmas. Rely strictly on standard Lean/Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).
3. **No Trivial Goal Stubs:** Never weaken theorem targets to `: True` or append `∧ True` placeholders.
4. **No Solver Timeouts Bypass:** Do not set `set_option maxHeartbeats 0` or artificially inflate heartbeat limits.
5. **Mandatory Verification Gate:** Run the following commands and ensure both exit with status `0`:
   ```bash
   lake build
   laud check src --entry Main
   laud mutate src --lake --vacuous-only --limit 100 --run
   ```
"#;

    let agents_path = dir.join("AGENTS.md");
    if let Err(e) = fs::write(&agents_path, policy) {
        eprintln!("Failed to write {:?}: {e}", agents_path);
        return ExitCode::from(2);
    }
    println!("Generated AI-agent guardrail file: {:?}", agents_path);

    if also_claude {
        let claude_path = dir.join("CLAUDE.md");
        if let Err(e) = fs::write(&claude_path, policy) {
            eprintln!("Failed to write {:?}: {e}", claude_path);
            return ExitCode::from(2);
        }
        println!("Generated Claude Code guardrail file: {:?}", claude_path);
    }

    ExitCode::SUCCESS
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Commands::Graph { src, entry, export_unique, tree, max_depth } => {
            graph::run_graph(&src, &entry, export_unique, tree, max_depth)
        }
        Commands::Check { src, entry, allow_axioms, filter, export_flagged } => {
            graph::run_check(&src, &entry, allow_axioms, filter, export_flagged)
        }
        Commands::InitAgent { dir, claude } => write_agent_instructions(&dir, claude),
        Commands::Mutate {
            path, out, filter, run, strip_imports, verify_orig, lake, vacuous_only, limit, lean_cmd,
        } => mutate::run_mutate(
            &path, &out, filter, run, strip_imports, verify_orig, lake, vacuous_only, limit, &lean_cmd,
        ),
        Commands::Slice { src, entry, max_depth, out, axioms, tree_shake, run } => {
            slice::run_slice(&src, &entry, max_depth, &out, axioms, tree_shake, run)
        }
        Commands::Blueprint {
            src, entry, max_depth, only_theorems, include_props, tex, md, tree_shake,
        } => blueprint::run_blueprint(
            &src, &entry, max_depth, only_theorems, include_props, tex, md, tree_shake,
        ),
    }
}
