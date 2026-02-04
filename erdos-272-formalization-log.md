# Erdős Problem 272 Formalization Log

## Problem Statement
Let N ≥ 1. Find the largest t such that there exist $A_1,...,A_t \subseteq \{1,...,N\}$ where $A_i \cap A_j$ is a non-empty arithmetic progression for all $i \neq j$.

## Status
**OPEN** (with significant progress by Szabo)

## Formalization Details

### Main Definitions
- `IsArithmeticProgression S`: Predicate for arithmetic progressions
- `max_t N`: The maximal number of sets with the desired property

### Key Theorems
1. `erdos_272.simonovits_sos_upper`: Simonovits and Sós proved $t \ll N^2$
2. `erdos_272.szabo`: Szabo proved $t = N^2/2 + O(N^{5/3}(\log N)^3)$
3. `erdos_272.szabo_lower`: Szabo's construction lower bound
4. `erdos_272.szabo_conjecture`: Szabo conjectures $t = \binom{N}{2} + O(N)$

### Category
- `@[category research solved, AMS 05]` for Szabo's results
- `@[category research open, AMS 05]` for Szabo's conjecture

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/272.lean`

## References
- Erdős and Graham (1980)
- Simonovits and Sós
- Szabo
- [erdosproblems.com/272](https://www.erdosproblems.com/272)
