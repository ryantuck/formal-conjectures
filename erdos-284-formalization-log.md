# Erdős Problem 284 Formalization Log

## Problem Statement
Let $f(k)$ denote the maximum value of $n_1$ such that there exist $n_1 < n_2 < \cdots < n_k$ satisfying: $1 = \frac{1}{n_1} + \cdots + \frac{1}{n_k}$. Is $f(k) = (1+o(1))\frac{k}{e-1}$?

## Status
**SOLVED** - Essentially solved by Croot (2001).

## Formalization Details

### Main Definitions
- `f k`: The maximum value of $n_1$

### Key Theorems
1. `erdos_284_upper_bound`: Trivial upper bound
2. `erdos_284_croot`: Croot's result
3. `erdos_284`: Main conjecture

### Category
- `@[category research solved, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/284.lean`

## References
- Erdős and Graham (1980)
- Croot (2001)
- [erdosproblems.com/284](https://www.erdosproblems.com/284)
