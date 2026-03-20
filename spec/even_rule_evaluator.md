# Canonical evaluator semantics — even closed-form rule

## Purpose
This file defines the canonical evaluation order for the even closed-form rule.

It does not yet provide an executable implementation.
Its role is to make the rule operationally unambiguous before the Lean layer is introduced.

## Inputs
- an even integer `m >= 8`
- coordinates `(i, j, k)` in `Z_m^3`

## Normalization conventions
Before evaluation:
- interpret `i`, `j`, and `k` modulo `m`
- compute the canonical representative of
  `s = i + j + k (mod m)`
  in `{0,1,...,m-1}`
- define `h = m / 2`

## Canonical evaluation order
The value `sigma(i,j,k)` is evaluated in the following order:

### Step 1 — trivial fibers
If `s <= m - 3`, return:

- `012`

### Step 2 — layer s = m - 1
If `s = m - 1`, return:

- `210`, if `i = h - 1` or `i = h`
- `120`, otherwise

### Step 3 — layer s = m - 2
If `s = m - 2`, return:

- `tau(i,j)`

where `tau(i,j)` is determined by the canonical source-locked artifacts:

- `spec/tau_layer_m_minus_2_table.md`
- `spec/tau_layer_m_minus_2_cases.json`

## Exhaustiveness
Since `s` is evaluated in `{0,1,...,m-1}`, the three branches above are exhaustive:
- `s <= m - 3`
- `s = m - 2`
- `s = m - 1`

No other case exists.

## Source traceability
This evaluator semantics is derived from:

- `spec/even_closed_form_source.md`
- `spec/tau_layer_m_minus_2_table.md`
- `spec/tau_layer_m_minus_2_cases.json`

These artifacts together define the canonical even rule for this repository.

## Repository policy
Any later executable implementation of the even rule
must be traceable to this evaluator semantics.

In particular:
- a Lean definition,
- a verifier implementation,
- or any generated lookup procedure

must preserve this exact branch order and source dependency.

## Next implementation layer
The next step after this file is:
- create the first Lean skeleton for the even rule
- separate the global branch logic from the `tau(i,j)` layer
- keep traceability to the source-locked artifacts above
