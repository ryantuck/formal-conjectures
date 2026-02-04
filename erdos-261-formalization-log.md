# Erdős Problem 261 Formalization Log

## Problem Statement
Two related questions about representations of rationals as sums of Egyptian fractions with powers of 2:

1. Are there infinitely many values of n such that there exist t ≥ 2 and distinct integers $a_1,...,a_t \geq 1$ satisfying: $n/2^n = \sum a_k/2^{a_k}$?

2. Does there exist a rational x such that $x = \sum a_k/2^{a_k}$ has at least $2^{\aleph_0}$ solutions?

## Status
- Question 1: **SOLVED** - Cusick proved infinitely many such n exist
- Question 2: **OPEN**

## Formalization Details

### Main Theorems
1. `erdos_261.infinitely_many`: Infinitely many n with the desired property (Cusick)
2. `erdos_261.borwein_loring`: For n = 2^(m+1) - m - 2, the equation holds
3. `erdos_261.continuum_representations`: Open question about continuum many representations

### Category
- `@[category research solved, AMS 11]` for first question
- `@[category research open, AMS 11]` for second question

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/261.lean`

## References
- Cusick
- Borwein and Loring (1990)
- Tengely, Ulas, Zygadlo (2020)
- [erdosproblems.com/261](https://www.erdosproblems.com/261)
