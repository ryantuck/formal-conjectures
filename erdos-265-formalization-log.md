# Erdős Problem 265 Formalization Log

## Problem Statement
Let $1 \leq a_1 < a_2 < \cdots$ be an increasing sequence of integers. How fast can $a_n \to \infty$ grow if both $\sum(1/a_n)$ and $\sum(1/(a_n-1))$ are rational?

## Status
**OPEN** (with significant progress)

## Formalization Details

### Main Theorems
1. `erdos_265`: Main question about achievable growth rates
2. `erdos_265.cantor_example`: Cantor's example $a_n = \binom{n}{2}$
3. `erdos_265.kovac_tao`: Kovač and Tao (2024) - doubly exponential growth possible
4. `erdos_265.necessary_condition`: Erdős's conjectured necessary condition

### Category
- `@[category research open, AMS 11]` for main question and necessary condition
- `@[category research solved, AMS 11]` for partial results

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/265.lean`

## References
- Erdős and Graham (1980)
- Cantor
- Kovač and Tao (2024)
- [erdosproblems.com/265](https://www.erdosproblems.com/265)
