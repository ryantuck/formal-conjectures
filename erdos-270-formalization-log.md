# Erdős Problem 270 Formalization Log

## Problem Statement
For a function $f(n) \to \infty$ as $n \to \infty$, is the sum
$$\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}$$
necessarily irrational?

## Status
**DISPROVED** - Crmarić and Kovač (2025) answered negatively.

## Formalization Details

### Main Theorems
1. `erdos_270`: The sum is not necessarily irrational
2. `erdos_270.crmovic_kovac`: For any α > 0, there exists f with the sum equal to α
3. `erdos_270.hansen`: Hansen's result that $\sum_n \frac{1}{\binom{2n}{n}}$ is transcendental
4. `erdos_270.nondecreasing_measure_zero`: If f is nondecreasing, possible values have measure zero

### Category
- `@[category research solved, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/270.lean`

## References
- Erdős and Graham (1980)
- Hansen (1975)
- Crmarić and Kovač (2025)
- [erdosproblems.com/270](https://www.erdosproblems.com/270)
