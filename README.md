# lean-audit (`laud`)

A high-speed DAG deduplicator, ASCII dependency tree visualizer, and proof mutation testing CLI for **Lean 4**, written in Rust.

Designed to audit large formalization repositories (including AI-generated Lean codebases) by pruning dead modules, deduplicating cloned definitions, and stress-testing theorems against vacuous truths, unused hypotheses, and boundary shifts.

## Installation

Install directly from [crates.io](https://crates.io) (provides both `laud` and `lean-audit` binaries):

```bash
cargo install lean-audit
```

## Quick Start & Examples

### 1. Deduplicate Import DAG & Render ASCII Tree (`laud graph`)

Traverse the import graph starting from `Main.lean`, collapse structurally identical files via content hashing, and visualize the dependency tree:

```bash
laud graph src --entry Main --tree --max-depth 3
```

**Example Output:**
```text
Deduplicated ASCII Dependency Tree (max depth: 3):
Main
├── Statements
│   └── Formalism.ZetaZeros
└── Development.MainTheorem
    ├── GroundTheory.BaseDefs
    ├── GroundTheory.BaseDefsCopy [dedup]
    └── Formalism.BridgeLemma [HEq, maxHeartbeats]
```

### 2. Mutation Testing on Lean 4 Theorems (`laud mutate`)

Suppose you have a Lean file `Example.lean` with a vacuous hypothesis or an unused assumption:

```lean
-- Example.lean
theorem vacuous_bound (x : Nat) (h1 : x < 5) (h2 : 10 < x) : x = 42 := by
  omega

theorem unused_assumption (n : Nat) (h_unused : 0 < n) : n + 0 = n := by
  simp
```

Run `laud mutate` against the file:

```bash
laud mutate Example.lean --run
```

**Example Output:**
```text
+------------------------------------+-----------+-----------------------+

| Mutation Category                  | Generated | Survived (Suspicious) |
+========================================================================+

| VACUOUS_TRUTH (Target -> False)    | 2         | 1                     |
|------------------------------------+-----------+-----------------------+

| UNUSED_HYP (Hypothesis Removal)    | 3         | 1                     |
|------------------------------------+-----------+-----------------------+

| BOUNDARY_SHIFT (Operator/Constant) | 1         | 0                     |
+------------------------------------+-----------+-----------------------+

SURVIVING MUTANTS DETECTED:
+---------------+------------------------+---------------------------------+

| Category      | Mutation               | Origin                          |
+==========================================================================+

| VACUOUS_TRUTH | Target -> False        | Example.lean:vacuous_bound      |
|---------------+------------------------+---------------------------------+

| UNUSED_HYP    | Drop (h_unused : 0 < n)| Example.lean:unused_assumption  |
+---------------+------------------------+---------------------------------+
```

### 3. Standalone Core-Only Mode (`--strip-imports` & `--verify-orig`)

Audit standalone lemmas without waiting for a full `Mathlib` build:

```bash
laud mutate src --strip-imports --verify-orig --run
```

## License

MIT License — Copyright (c) 2026 Alexander Limanskii.
