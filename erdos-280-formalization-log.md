# Erdős Problem 280 Formalization Log

## Problem Statement
Let $n_1 < n_2 < \cdots$ be an infinite sequence of integers with associated $a_k \pmod{n_k}$, such that for some $\epsilon > 0$ we have $n_k > (1+\epsilon)k\log k$ for all $k$. Must the number of uncovered integers be non-negligible?

## Status
**DISPROVED** - Counterexample: $n_k = 2^k$ and $a_k = 2^{k-1} + 1$ yields only $m=1$ uncovered.

## Formalization Details

### Main Theorems
1. `erdos_280`: The conjecture is false
2. `erdos_280.counterexample`: Explicit counterexample

### Category
- `@[category research solved, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/280.lean`

## References
- Erdős and Graham (1980)
- [erdosproblems.com/280](https://www.erdosproblems.com/280)
