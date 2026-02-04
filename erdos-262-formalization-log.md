# Erdős Problem 262 Formalization Log

## Problem Statement
Suppose $a_1 < a_2 < \cdots$ is a sequence of integers such that for all integer sequences $t_n$ with $t_n \geq 1$ the sum $\sum_{n=1}^{\infty} \frac{1}{t_n a_n}$ is irrational. How slowly can $a_n$ grow?

## Status
**SOLVED** - Hančl (1991) characterized the growth rate.

## Formalization Details

### Main Definition
- `IsIrrationalitySequence a`: Predicate for irrationality sequences

### Key Theorems
1. `erdos_262.hancl_lower_bound`: Hančl's result that $\limsup_{n \to \infty} \frac{\log_2 \log_2 a_n}{n} \geq 1$
2. `erdos_262.general_obstruction`: General obstruction for slowly growing sequences
3. `erdos_262.double_exponential`: $a_n = 2^{2^n}$ is an irrationality sequence

### Category
- `@[category research solved, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/262.lean`

## References
- Erdős and Graham (1980)
- Hančl (1991)
- [erdosproblems.com/262](https://www.erdosproblems.com/262)
