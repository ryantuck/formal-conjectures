# Erdős Problem 293 Formalization Log

## Problem Statement
Let k ≥ 1 and let v(k) be the minimal integer which does not appear as some $n_i$ in a solution to: $1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$ with $1\leq n_1<\cdots <n_k$. Estimate the growth of v(k).

## Status
**OPEN** (with significant progress on bounds)

## Formalization Details

### Main Definitions
- `v k`: The minimal integer not appearing in any representation

### Key Theorems
1. `erdos_293.lower_bound_factorial`: Bleicher and Erdős proved $v(k) \gg k!$
2. `erdos_293.upper_bound_vardi`: Upper bound $v(k) \leq kc_0^{2^k}$ (Vardi constant)
3. `erdos_293.van_doorn_tang`: van Doorn and Tang proved $v(k) \geq e^{ck^2}$
4. `erdos_293`: Open question about precise growth rate

### Category
- `@[category research solved, AMS 11]` for bounds
- `@[category research open, AMS 11]` for precise asymptotics

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/293.lean`

## References
- Erdős and Graham (1980)
- Bleicher and Erdős
- van Doorn and Tang
- [erdosproblems.com/293](https://www.erdosproblems.com/293)
