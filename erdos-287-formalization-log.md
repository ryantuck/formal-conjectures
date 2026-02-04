# Erdős Problem 287 Formalization Log

## Problem Statement
Let k ≥ 2. For any distinct integers $1 < n_1 < \cdots < n_k$ satisfying $1 = 1/n_1 + \cdots + 1/n_k$, must we have $\max(n_{i+1} - n_i) \geq 3$?

## Status
**OPEN** (with partial result from Erdős, 1932)

## Formalization Details

### Main Theorems
1. `erdos_287`: Main conjecture
2. `erdos_287_gap_two`: Erdős (1932) proved the lower bound ≥ 2

### Category
- `@[category research open, AMS 11]` for main conjecture
- `@[category research solved, AMS 11]` for Erdős's result

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/287.lean`

## References
- Erdős (1932)
- Erdős and Graham (1980)
- [erdosproblems.com/287](https://www.erdosproblems.com/287)
