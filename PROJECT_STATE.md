# Project State — Claude Cycles / ARZN 

## Current baseline 
- Paper version: [substituir pelo nome exato do docx atual] 
- Repo status: CI green 
- Current phase: M3 canonical even rule 
- Last green commit: 82b83c8 
- Last repo fix: removed corrupted `lake-manifest.json` 

## Completed milestones 
- M0: Lean scaffold 
- M1: torus, fibers, and fiber shift 
- M2a: return map and fiber preservation 
- M2b: orbit algebra and block decomposition 
- M2c: factorization from `F0` into return iterates plus residual displacement 
- M2d: partial global lift from return reachability in `F0` 
- M2e: conditional strong reduction from return coverage to global reachability 

## Canonical sources locked 
- Odd canonical source: `Claude’s Cycles` 
- Even canonical source: `A proof for the even closed-form rule in Claude’s Cycles` 
- Alternative odd source: `An Alternative Hamiltonian Decomposition of the Three-Dimensional Torus Digraph` 

## Spec artifacts already created 
- `spec/even_closed_form_source.md` 
- `spec/tau_layer_m_minus_2_table.md` 
- `spec/tau_layer_m_minus_2_cases.json` 
- `spec/even_rule_evaluator.md` 

## Lean artifacts already created 
- `ClaudeCyclesARZN/EvenRule.lean` 
- `ClaudeCyclesARZN/EvenRuleFacts.lean` 
- `ClaudeCyclesARZN/EvenExceptionalFibers.lean` 

## Entry-point imports already updated 
- `ClaudeCyclesARZN.lean` already imports: 
- `EvenRule` - `EvenRuleFacts` 
- `EvenExceptionalFibers` 

## Infrastructure note 
- The previous `lake-manifest.json` in `ClaudeCyclesARZN_Lean_M0/` was corrupted and was removed. 
- CI turned green after removing it. 
- Do not reintroduce `lake-manifest.json` manually. 

## Current theorem boundary 
- Structural abstract reduction layer: validated in Lean 
- Canonical even rule: frozen as source of truth 
- Machine-readable `tau(i,j)` table: created 
- Canonical evaluator semantics: created 
- Even-rule Lean skeleton: created 
- Branch lemmas for the even rule: created 
- Exceptional-fiber bridge: created 
- Residual-support bridge: not yet created 
- Residual normal form shell: not yet created - Final Hamiltonicity closure for the canonical even rule: not yet proven in Lean 

## Exact next step Create: 
- `ClaudeCyclesARZN_Lean_M0/ClaudeCyclesARZN/EvenResidualSupport.lean` Then add to: 
- `ClaudeCyclesARZN_Lean_M0/ClaudeCyclesARZN.lean` the import: 
- `import ClaudeCyclesARZN.EvenResidualSupport` 

## What the next step must do The next file should formalize the bridge: 
- residual support = exceptional fibers - outside residual support, the even rule is trivial (`012`) 
- on residual support, the rule is exactly the controlled nontrivial behavior 
- this is the preparatory shell before the residual normal form layer 

## Paper / docx policy at this checkpoint 
- No docx update is required for the micro-step `EvenResidualSupport` 
- The next docx update should happen only after the next stable Lean checkpoint is green 

## Working rule for next chat In the next chat: 1. trust this file as source of truth 2. do not revisit GitHub configuration 3. do not revisit M0/M1/M2 unless a new CI error forces it 4. continue exactly from the next file: `EvenResidualSupport.lean` 

## Suggested checkpoint label 
- `v6-m3-pre-residual-support` ```
