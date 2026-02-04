# Erdős Problem 260 Formalization Log

## Problem Statement
Let $a_1 < a_2 < \cdots$ be an increasing sequence such that $\frac{a_n}{n} \to \infty$.
Is the sum $\sum_n \frac{a_n}{2^{a_n}}$ irrational?

## Status
**OPEN**

## Formalization Details

### Main Theorems
1. `erdos_260`: Main conjecture that the sum is irrational under the weak condition
2. `erdos_260.gap_condition`: Erdős proved irrationality when $a_{n+1} - a_n \to \infty$
3. `erdos_260.strong_growth`: Erdős proved irrationality when $a_n \gg n\sqrt{\log n \log \log n}$

### Category
- `@[category research open, AMS 11]` for main conjecture
- `@[category research solved, AMS 11]` for partial results

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/260.lean`

## References
- Erdős (1974)
- [erdosproblems.com/260](https://www.erdosproblems.com/260)
