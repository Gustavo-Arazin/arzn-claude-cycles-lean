# Canonical source — even closed-form rule

## Locked source
This repository treats the note **“A proof for the even closed-form rule in Claude’s Cycles”** as the canonical source of truth for the even case.

## Scope
The source proves that the closed-form C rule in `even_closed_form.c` defines, for every even integer `m >= 8`, a decomposition of the directed `m x m x m` torus into three directed Hamiltonian cycles.

## Rule skeleton
Fix an even integer `m >= 8`, and write `h = m / 2`.

Let
`s = i + j + k (mod m)`,

where comparisons with `m - 2` and `m - 1` use the canonical representative in `{0,1,...,m-1}`.

Then the rule is:

- `sigma(i,j,k) = 012`, if `s <= m - 3`
- `sigma(i,j,k) = 210`, if `s = m - 1` and `i in {h - 1, h}`
- `sigma(i,j,k) = 120`, if `s = m - 1` and `i not in {h - 1, h}`
- `sigma(i,j,k) = tau(i,j)`, if `s = m - 2`

## Structural fact
Only the last two fibers `F_{m-2}` and `F_{m-1}` are nontrivial.
On every other fiber the rule is simply `012`.

This means:
- the default return-map behavior is almost trivial;
- the only nontrivial splice occurs in the last two fibers;
- the table `tau(i,j)` is the canonical object that must be frozen before implementation.

## Repository policy
This file is the human-readable source lock for the even rule.
The machine-readable transcription of `tau(i,j)` is maintained separately in:

- `spec/tau_layer_m_minus_2_table.md`

## Implementation policy
No Lean implementation of the even rule should be treated as canonical unless it is traceable to:
1. this source file, and
2. the explicit `tau(i,j)` table transcription.
