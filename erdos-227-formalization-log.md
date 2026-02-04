# Erdős Problem 227 - Formalization Log

## Problem Statement

Let $f=\sum_{n=0}^\infty a_nz^n$ be an entire function which is not a polynomial. Is it true that if
$$\lim_{r\to \infty} \frac{\max_n|a_nr^n|}{\max_{|z|=r}|f(z)|}$$
exists, then it must be $0$?

## Status

**DISPROVED**

## Key Results

- **Clunie (unpublished)**: Proved this is true if $a_n\geq 0$ for all $n$
- **Clunie and Hayman [ClHa64]**: Disproved in general - showed the limit can take any value in $[0,1/2]$

## Formalization Details

### Main Components

1. **`coefficientRatio`**: Defines the ratio $\frac{\max_n|a_nr^n|}{\max_{|z|=r}|f(z)|}$ as a function of $r$

2. **Main theorem `erdos_227`**: Shows that NOT all entire non-polynomial functions have this limit equal to 0 when it exists

3. **`erdos_227.clunie_positive`**: Clunie's result for non-negative coefficients - in this special case, if the limit exists, it must be 0

## Counterexample Result

The Clunie-Hayman construction shows that for any $L \in [0, 1/2]$, there exists an entire function where this limit equals $L$.

## Technical Notes

- Uses complex analysis and filter theory for limits
- The supremum over the circle $|z|=r$ captures the maximum modulus principle
- The formalization captures both the negative result (main theorem) and the positive special case (Clunie's result)

## References

- [ClHa64] Clunie, J. and Hayman, W. K., _The maximum term of a power series_. J. d'Analyse Math. (1964), 439-505.

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/227.lean`
