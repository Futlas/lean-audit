# lean-audit (`laud`)

A high-speed DAG deduplicator, ASCII dependency tree visualizer, arXiv-style LaTeX proof outline generator, and proof mutation testing CLI for **Lean 4**, written in Rust.

Designed to audit massive formalization repositories (including AI-generated Lean codebases) by pruning dead modules, deduplicating cloned definitions, extracting human-readable LaTeX proof outlines with tactic-based proof sketches, and stress-testing theorems against vacuous truths and unused hypotheses.

## Installation

Install directly from [crates.io](https://crates.io) (provides both `laud` and `lean-audit` executables):

```bash
cargo install lean-audit
```

## Subcommands & Examples

### 1. Deduplicate Import DAG & Render ASCII Tree (`laud graph`)

Traverse the import graph starting from `Main.lean`, collapse structurally identical files via content hashing, flag `HEq` bridges and `maxHeartbeats` overrides, and render an ASCII dependency tree:

```bash
laud graph src --entry Main --tree --max-depth 4
```

### 2. Offline arXiv-Style LaTeX Proof Outline (`laud blueprint`)

Extract docstrings (`/-- ... -/`), clean up typeclass/namespace noise, summarize proof tactics and term reductions (`induction`, `by_contra`, `omega`, `linarith`, `simp`), and export a ready-to-compile LaTeX article (`.tex`) without relying on external LLMs:

```bash
laud blueprint src --entry Main --max-depth 3 --tex proof_outline.tex
pdflatex proof_outline.tex
```

### 3. Proof Mutation Testing & CI Integration (`laud mutate`)

Run parallel mutation testing (`VACUOUS_TRUTH`, `UNUSED_HYP`, `BOUNDARY_SHIFT`) with automatic Lake workspace detection (`--lake`) and CI exit codes (`exit 1` if any mutant survives):

```bash
# Run inside a Lake/Mathlib project
laud mutate src --lake --run

# Run standalone core-only checks without Mathlib
laud mutate src --strip-imports --verify-orig --run
```

## License

MIT License — Copyright (c) 2026 Alexander Limanskii.
