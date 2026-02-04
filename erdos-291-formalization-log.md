# Erdős Problem 291 Formalization Log

## Problem Statement
Let $n \geq 1$ and define $L_n$ as the least common multiple of $\{1, \ldots, n\}$ and $a_n$ by: $\sum_{1 \leq k \leq n} \frac{1}{k} = \frac{a_n}{L_n}$. Is it true that both $(a_n, L_n) = 1$ and $(a_n, L_n) > 1$ occur for infinitely many $n$?

## Status
**OPEN** (with conditional results)

## Formalization Details

### Main Definitions
- `L n`: Least common multiple of $\{1, \ldots, n\}$
- `a n`: Numerator of the harmonic sum

### Key Theorems
1. `erdos_291`: Main question
2. `erdos_291.wu_yan_conditional`: Wu-Yan (2022) conditional result

### Category
- `@[category research open, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/291.lean`

## References
- Erdős and Graham (1980)
- Steinerberger
- Shiu
- Wu and Yan (2022)
- [erdosproblems.com/291](https://www.erdosproblems.com/291)
