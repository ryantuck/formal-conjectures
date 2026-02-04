# Erdős Problem 290 Formalization Log

## Problem Statement
Let $a \geq 1$. Must there exist some $b > a$ such that the denominator of $\sum_{a \leq n \leq b+1} 1/n$ (in reduced form) is less than the denominator of $\sum_{a \leq n \leq b} 1/n$?

## Status
**SOLVED** - Van Doorn (2024) resolved this affirmatively.

## Formalization Details

### Main Definitions
- `harmonic_sum a b`: The sum of reciprocals from a to b

### Key Theorems
1. `erdos_290`: Van Doorn's main result
2. `erdos_290.van_doorn_upper`: Upper bound $b(a) < 4.374a$ for $a > 1$
3. `erdos_290.van_doorn_lower`: Lower bound $b(a) > a + 0.54\log a$ for large $a$

### Category
- `@[category research solved, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/290.lean`

## References
- Erdős and Graham (1980)
- Van Doorn (2024)
- [erdosproblems.com/290](https://www.erdosproblems.com/290)
