# Erdős Problem 281 Formalization Log

## Problem Statement
Let $n_1<n_2<\cdots$ be an infinite sequence such that for any choice of congruence classes $a_i\pmod{n_i}$, the set of integers not satisfying any of the congruences has density $0$. For every $\epsilon>0$ does there exist $k$ such that the density is less than $\epsilon$ for the first $k$ congruences?

## Status
**SOLVED** - The answer is affirmative and has been verified in Lean.

## Formalization Details

### Main Theorems
1. `erdos_281`: Main theorem

### Category
- `@[category research solved, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/281.lean`

## References
- Erdős and Graham (1980)
- [erdosproblems.com/281](https://www.erdosproblems.com/281)
