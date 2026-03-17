[![ci](https://github.com/Gustavo-Arazin/arzn-claude-cycles-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/Gustavo-Arazin/arzn-claude-cycles-lean/actions/workflows/ci.yml)
# ClaudeCyclesARZN (Lean4) — Milestone M0

This repository is a **construction-agnostic** Lean4 scaffolding for formalizing the verification logic
used in the Claude's Cycles paper-lineage.

## Pinned toolchain (recommended)
- Lean toolchain: `leanprover/lean4:v4.27.0`
- Mathlib: `leanprover-community/mathlib4 @ v4.27.0`

If you need to change versions, follow Mathlib guidance on pinning `rev` in `lakefile.toml`.

## Build (local)
1) Install `elan`.
2) In the project root:
   - `lake update`
   - `lake exe cache get`  (optional but recommended)
   - `lake build`

To build only the core file:
- `lake build ClaudeCyclesARZN.Core`

## What is proven in M0
- Definitions of successor-induced arc-sets, arc-disjointness, and Hamiltonicity-as-single-orbit.
- Lemmas that: injectivity ⇒ uniqueness of preimages; bijectivity ⇒ existence/uniqueness of predecessors.
- A 3-color predicate `ThreeSucc.IsValid` capturing the verifier’s sufficient conditions.

## Next milestones (planned)
- M1: define the torus bump edges and local rule `σ`, derive successor maps `succ_c`.
- M2: implement the even closed-form rule as a Lean function, prove local distinctness and bijectivity.
- M3: prove single-orbit (Hamiltonicity) via fiber decomposition and return-map arguments.

