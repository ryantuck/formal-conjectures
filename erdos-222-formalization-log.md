# Erdős Problem 222 - Formalization Log

## Problem Statement

Explore the behaviour of the consecutive differences $n_{k+1} - n_k$ where $n_1 < n_2 < \dots$ are the integers which are the sum of two squares. In particular, is it true that $n_{k+1} - n_k < C(n_k)^{1/4}$ for all sufficiently large $k$?

## Status

**OPEN**

## Key Results

1. **Lower bound (Erdős, 1951)**: For infinitely many $k$,
   $$n_{k+1}-n_k \gg \frac{\log n_k}{\sqrt{\log\log n_k}}$$

2. **Improved lower bound (Richards, 1982)**:
   $$\limsup_{k \to \infty} \frac{n_{k+1}-n_k}{\log n_k} \geq 1/4$$

3. **Upper bound (Bambah and Chowla, 1947)**:
   $$n_{k+1} - n_k \ll n_k^{1/2}$$

## Formalization Details

### Main Components

1. **`IsSumOfTwoSquares`**: A natural number is a sum of two squares if $n = x^2 + y^2$ for some $x, y \in \mathbb{N}$

2. **`S`**: The set of all integers that are sums of two squares

3. **`n_`**: The sequence of integers that are sums of two squares in increasing order

4. **Main conjecture `erdos_222`**: Upper bound conjecture $n_{k+1} - n_k < C(n_k)^{1/4}$

### Theorems Formalized

- `erdos_222.lb`: Erdős lower bound
- `erdos_222.richards_lb`: Richards improved lower bound
- Additional upper bounds from Bambah and Chowla

## References

- [Er51] Erdős, P., _On the sum of two squares_. J. London Math. Soc. (1951), 244-247.
- [Ri82] Richards, I., _On the gaps between numbers which are sums of two squares_. Adv. in Math. (1982), 1-2.
- [BaCh47] Bambah and Chowla

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/222.lean`
