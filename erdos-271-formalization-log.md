# Erdős Problem 271 Formalization Log

## Problem Statement
Let $A(n)=\{a_0<a_1<\cdots\}$ be the sequence defined by $a_0=0$ and $a_1=n$. For $k\geq 1$, define $a_{k+1}$ as the least positive integer such that $\{a_0,\ldots,a_{k+1}\}$ contains no three-term arithmetic progression.

Can the $a_k$ be explicitly determined? How fast do they grow?

## Status
**OPEN** (with partial results)

## Formalization Details

### Main Definitions
- `A n k`: The Stanley sequence starting with 0 and n

### Key Theorems
1. `erdos_271.A_one_characterization`: $A(1)$ comprises integers with no digit 2 in base-3 expansion
2. `erdos_271.moy_upper_bound`: Moy's upper bound $a_k \leq \frac{(k-1)(k+2)}{2}+n$
3. `erdos_271.growth_rate`: Open question about the growth rate

### Category
- `@[category research solved, AMS 11]` for partial results
- `@[category research open, AMS 11]` for growth rate question

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/271.lean`

## References
- Erdős and Graham (1980)
- Odlyzko and Stanley
- Moy (2011)
- [erdosproblems.com/271](https://www.erdosproblems.com/271)
