# lean-audit

A high-speed DAG deduplicator and proof mutation testing CLI for **Lean 4**, written in Rust.

Designed to audit massive formalization repositories (including AI-generated Lean codebases) by pruning dead modules, deduplicating cloned definitions, and stress-testing theorems against vacuous truths and unused hypotheses.

## Features
- **`graph` subcommand**: Traverses the import DAG starting from an entry module (`Main`), deduplicates cloned files via structural content hashing, maps `HEq` bridges and `maxHeartbeats` overrides by depth, and exports the deduplicated module list.
- **`mutate` subcommand**: Generates three classes of proof mutants in parallel using `rayon`:
  - `VACUOUS_TRUTH`: Replaces the theorem target with `False` and runs core tactics (`omega`, `contradiction`, `decide`, `simp`) to detect contradictory hypotheses.
  - `UNUSED_HYP`: Removes explicit hypotheses one by one while keeping the original proof intact.
  - `BOUNDARY_SHIFT`: Weakens or inverts operators and constants (`<` -> `≤`, `=` -> `≠`, `1 / 2` -> `1 / 4`).
- **`--verify-orig` & `--strip-imports`**: Filters out uncompilable files prior to mutation or strips `import` statements for standalone core-only auditing.

## Build & Usage
```bash
cargo build --release

# 1. Deduplicate and analyze the import DAG
./target/release/lean-audit graph ../src --entry Main --export-unique /tmp/unique_modules.txt

# 2. Run proof mutation testing on a target directory
./target/release/lean-audit mutate ./tests --run

# 3. Audit core-only lemmas in offline mode without Mathlib
./target/release/lean-audit mutate ../src --strip-imports --verify-orig --run
```
