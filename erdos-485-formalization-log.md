# Erdős Problem 485 - Formalization Log

## Problem Statement

Let f(k) be the minimum number of terms in P(x)², where P ∈ ℚ[x] ranges over all polynomials with exactly k non-zero terms.

**Question:** Is it true that f(k) → ∞ as k → ∞?

## Status

PROVED - The conjecture has been confirmed affirmatively.

## Known Results

- Erdős: f(k) < k^(1-c) for some constant c > 0
- Schinzel: f(k) > log log k / log 2
- Schinzel-Zannier: f(k) ≫ log k

## Formalization Approach

1. **Term counting** (`termCount`):
   - Defined as cardinality of polynomial support (non-zero coefficients)

2. **Minimum function** (`minSquareTerms`):
   - f(k) = infimum of term counts in P² over all k-term polynomials P

3. **Main theorem** (`minSquareTerms_diverges`):
   - States f(k) → ∞ using Filter.Tendsto

4. **Bounds**:
   - Schinzel's bound: f(k) > log log k / log 2
   - Schinzel-Zannier: f(k) ≫ log k (asymptotic lower bound)
   - Erdős upper bound: f(k) < k^(1-c)

## Technical Notes

- Used Polynomial.support.card for counting terms
- Used Filter.Eventually for asymptotic statements
- sInf used for minimum definition (would need nonempty/bounded proof in full formalization)

## References

- Erdős and Rényi (original conjecture)
- Schinzel (first positive result)
- Schinzel and Zannier (improved bound)
- Halberstam, Problem 4.4
