# lean-audit (`laud`)

[![Crates.io](https://shields.io/crates/v/lean-audit.svg)](https://crates.io/crates/lean-audit)
[![License: MIT](https://shields.io/badge/License-MIT-blue.svg)](LICENSE)

A high-speed DAG deduplicator, ASCII dependency tree visualizer, offline arXiv-style LaTeX proof outline generator, and proof mutation testing CLI for **Lean 4**, written in Rust.

Designed to audit massive formalization repositories (including AI-generated Lean codebases) by pruning dead modules, deduplicating cloned definitions, extracting human-readable LaTeX proof outlines with tactic-based proof sketches, and stress-testing theorems against vacuous truths and unused hypotheses.

## Installation

Install directly from [crates.io](https://crates.io/crates/lean-audit) (provides both `laud` and `lean-audit` executables):

```bash
cargo install lean-audit
```

---

## Features & Real-World Benchmarks

### 1. Import DAG Deduplication & ASCII Tree (`laud graph`)

Traverse the import graph starting from `Main.lean`, collapse structurally identical files via normalized AST-token hashing, flag `HEq` bridges and `maxHeartbeats` overrides, and render a deduplicated ASCII dependency tree:

```bash
laud graph src --entry Main --tree --max-depth 4
```

**Example Output (tested on a 175k-file formalization archive in ~1s):**
```text
Deduplicated ASCII Dependency Tree (max depth: 4):
Main
├── Statements
└── Supplements.Kernels.MainTheoremsAll
    ├── Supplements.Kernels.MainTheoremsCritical [dedup]
    └── Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf
        ├── Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree
        ├── Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TopMainZj
        │   └── ...DiscreteSeriesCoefficientsCuspidal [dedup]
        ├── Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.DefiniteNHolds
        └── Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

Total files on disk: 175083 | Reachable from `Main`: 169842 | Unique DAG nodes: 169473 (deduplicated 369 clones)
```

---

### 2. Offline arXiv-Style LaTeX Proof Outline (`laud blueprint`)

Extract docstrings (`/-- ... -/`), strip typeclass/namespace noise, summarize proof tactics (`induction`, `by_contra`, `omega`, `linarith`, `simp`) along with intermediate `have` claims, and export a ready-to-compile LaTeX article (`.tex`) **without relying on external LLMs**:

```bash
laud blueprint src --entry Main --max-depth 3 --tex proof_outline.tex
pdflatex proof_outline.tex
```

**Generated LaTeX Output Preview:**

![Generated LaTeX Proof Outline Preview](docs/blueprint_preview.png)

---

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
