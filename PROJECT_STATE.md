# Project State — Claude Cycles / ARZN

## Current baseline
- Paper version: ARZN_paper_claude_cycles_m_par_v6_M3.docx
- Repo status: CI green
- Lean milestone completed: M2e
- Current phase: M3 canonical even rule

## Completed milestones
- M0: Lean scaffold
- M1: torus, fibers, and fiber shift
- M2a: return map and fiber preservation
- M2b: orbit algebra and block decomposition
- M2c: factorization from F0 into return iterates plus residual displacement
- M2d: partial global lift from return reachability in F0
- M2e: conditional strong reduction from return coverage to global reachability

## Canonical sources locked
- Odd canonical source: Claude’s Cycles
- Even canonical source: A proof for the even closed-form rule in Claude’s Cycles
- Alternative odd source: An Alternative Hamiltonian Decomposition of the Three-Dimensional Torus Digraph

## Current paper architecture
- Main paper structure stabilized
- Appendix B contains Lean milestones
- Appendix C reserved for canonical rule tables and case splits

## Current theorem boundary
- Structural abstract reduction layer: validated in Lean
- Canonical even rule: frozen in the paper as source of truth
- Machine-readable tau(i,j) table: not yet created
- EvenRule Lean formalization: not yet started
- Residual normal form for the canonical even rule: not yet proven
- Final Hamiltonicity closure for the canonical even rule: not yet proven in Lean

## Open mathematical targets
- Freeze Appendix A tau(i,j) into a canonical machine-readable artifact
- Create:
  - spec/even_closed_form_source.md
  - spec/tau_layer_m_minus_2_table.md
- Prepare EvenRule Lean skeleton
- Prove the residual normal form hypothesis for the canonical even rule
- Connect the canonical even rule to the strong reduction framework
- Advance toward Hamiltonicity closure in Lean

## Next exact step
- Build canonical specification artifacts for the even closed-form rule
- Then prepare the first EvenRule implementation layer

## Most recent confirmed status
- Docx reorganized into fixed final architecture
- Claim Log updated, including C4a and C4b
- CI green after StrongReduction.lean
- M3 source-of-truth section inserted into Appendix B
- Appendix C reserved for tau(i,j)

## Files most recently changed
- docx: ARZN_paper_claude_cycles_m_par_v6_M3.docx
- Lean: StrongReduction.lean
- entrypoint updated accordingly
- CI workflow passing

## Working rule
When continuing in a new chat, use this file together with:
1. the latest docx
2. the current CI status
3. the name of the current milestone

## Current checkpoint tag suggestion
- v6-m3-baseline
