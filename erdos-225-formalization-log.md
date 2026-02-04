# Erdős Problem 225 - Formalization Log

## Problem Statement

Let $f(\theta) = \sum_{0\leq k\leq n}c_k e^{ik\theta}$ be a trigonometric polynomial all of whose roots are real, such that $\max_{\theta\in [0,2\pi]}|f(\theta)|=1$. Then $\int_0^{2\pi}|f(\theta)| d\theta \leq 4$.

## Status

**PROVED**

## Key Results

- **Kristiansen [Kr74]**: Proved for real coefficients $c_k \in \mathbb{R}$
- **Saff and Sheil-Small [SaSh74]**: Proved for general complex coefficients $c_k \in \mathbb{C}$

## Formalization Details

### Main Components

1. **`IsTrigonometricPolynomial`**: Defines a trigonometric polynomial as a finite sum $f(\theta) = \sum_{k=0}^n c_k e^{ik\theta}$

2. **`HasAllRealRoots`**: All roots of the function are real (imaginary part is zero)

3. **Main theorem `erdos_225`**: If a trigonometric polynomial has all real roots and maximum absolute value 1, then its $L^1$ norm over $[0, 2\pi]$ is at most 4

## Technical Notes

- Uses complex analysis and measure theory
- The integral is computed using Lean's measure theory library
- The supremum is taken over the interval $[0, 2\pi]$

## References

- [Kr74] Kristiansen, G. K., _On a problem of Erdős and Halmos_. Det. Kon. Norske Vid. Selskabs Skrifter (1974), 1-6.
- [SaSh74] Saff, E. B. and Sheil-Small, T., _Coefficient and integral mean estimates for algebraic and trigonometric polynomials with restricted zeros_. J. London Math. Soc. (1974), 16-22.

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/225.lean`
