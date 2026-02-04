# Erdős Problem 256 Formalization Log

## Problem Statement
Let $n \geq 1$ and $f(n)$ be maximal such that for any integers $1 \leq a_1 \leq \cdots \leq a_n$:
$$\max_{|z|=1}\left|\prod_{i}(1-z^{a_i})\right| \geq f(n)$$

The problem asks to estimate $f(n)$, specifically whether there exists a constant $c > 0$ such that $\log f(n) \gg n^c$.

## Status
**SOLVED** - The question was answered negatively by Belov and Konyagin (1996).

## Formalization Details

### Main Definition
- `f n`: The maximal value as defined in the problem statement

### Key Theorems
1. `erdos_256.limit_power`: Erdős and Szekeres proved $\lim f(n)^{1/n} = 1$
2. `erdos_256.lower_bound`: Erdős and Szekeres proved $f(n) > \sqrt{2n}$
3. `erdos_256`: Main theorem stating there is no $c > 0$ with $\log f(n) \gg n^c$
4. `erdos_256.belov_konyagin`: Upper bound $\log f(n) \ll (\log n)^4$

### Category
- `@[category research solved, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/256.lean`

## References
- Erdős and Szekeres (1959)
- Atkinson (1961)
- Odlyzko (1982)
- Belov and Konyagin (1996)
- [erdosproblems.com/256](https://www.erdosproblems.com/256)
