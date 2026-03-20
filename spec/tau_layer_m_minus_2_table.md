# Canonical tau(i,j) table for the layer s = m - 2

This file freezes the exact mathematical transcription of the layer
`s = m - 2` from Appendix A of the canonical source.

## Conventions
- `m` is even and `m >= 8`
- `h = m / 2`
- all arithmetic is in `Z_m` unless stated otherwise
- `tau(i,j)` is one of:
  - `012`
  - `021`
  - `102`
  - `120`
  - `201`
  - `210`

## Table

### Row i = 0
- if `j = m - 2`, then `tau(i,j) = 210`
- if `j = m - 1`, then `tau(i,j) = 102`
- otherwise, `tau(i,j) = 012`

### Row i = 1
- if `j = m - 2`, then `tau(i,j) = 201`
- if `j = m - 1`, then `tau(i,j) = 210`
- otherwise, `tau(i,j) = 012`

### Rows 2 <= i <= h - 3
- if `j = m - 1 - i`, then `tau(i,j) = 102`
- if `j = m - 1`, then `tau(i,j) = 210`
- otherwise, `tau(i,j) = 012`

### Row i = h - 2
- if `j <= h`, then `tau(i,j) = 021`
- if `j = h + 1`, then `tau(i,j) = 120`
- if `j = m - 2` and `m ≡ 0 (mod 4)`, then `tau(i,j) = 012`
- if `j = m - 2` and `m ≡ 2 (mod 4)`, then `tau(i,j) = 102`
- if `j = m - 1` and `m ≡ 0 (mod 4)`, then `tau(i,j) = 201`
- if `j = m - 1` and `m ≡ 2 (mod 4)`, then `tau(i,j) = 021`
- otherwise, `tau(i,j) = 012`

### Row i = h - 1
- if `j <= h - 1`, then `tau(i,j) = 021`
- if `j = h`, then `tau(i,j) = 120`
- if `h + 1 <= j <= m - 3`, then `tau(i,j) = 021`
- if `j = m - 2` and `m ≡ 0 (mod 4)`, then `tau(i,j) = 021`
- if `j = m - 2` and `m ≡ 2 (mod 4)`, then `tau(i,j) = 201`
- if `j = m - 1` and `m ≡ 0 (mod 4)`, then `tau(i,j) = 201`
- if `j = m - 1` and `m ≡ 2 (mod 4)`, then `tau(i,j) = 021`

### Row i = h
- if `j <= h - 2`, then `tau(i,j) = 021`
- if `j = h - 1`, then `tau(i,j) = 120`
- if `h <= j <= m - 3`, then `tau(i,j) = 021`
- if `j = m - 2` and `m ≡ 0 (mod 4)`, then `tau(i,j) = 021`
- if `j = m - 2` and `m ≡ 2 (mod 4)`, then `tau(i,j) = 201`
- if `j = m - 1` and `m ≡ 0 (mod 4)`, then `tau(i,j) = 201`
- if `j = m - 1` and `m ≡ 2 (mod 4)`, then `tau(i,j) = 021`

### Row i = h + 1
- if `j <= h - 3`, then `tau(i,j) = 012`
- if `j = h - 2`, then `tau(i,j) = 102`
- if `h - 1 <= j <= m - 3`, then `tau(i,j) = 021`
- if `j = m - 2` and `m ≡ 0 (mod 4)`, then `tau(i,j) = 120`
- if `j = m - 2` and `m ≡ 2 (mod 4)`, then `tau(i,j) = 210`
- if `j = m - 1`, then `tau(i,j) = 012`

### Rows h + 2 <= i <= m - 1
- if `j = m - 1 - i`, then `tau(i,j) = 102`
- if `j = m - 2`, then `tau(i,j) = 210`
- otherwise, `tau(i,j) = 012`

## Notes
This file is intentionally human-readable and source-locked.
A later artifact may translate this table into machine-readable form
(JSON, CSV, or code), but this file is the canonical textual specification
used for auditability and implementation traceability.
