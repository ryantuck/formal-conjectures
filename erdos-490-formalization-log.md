# Erdős Problem 490 - Formalization Log

## Problem Statement

Let A,B ⊆ {1,...,N} such that all products ab (with a ∈ A, b ∈ B) are distinct.
The question asks whether |A||B| ≪ N²/log N.

## Status

PROVED - Szemerédi (1976)

## Formalization Approach

1. **Distinct products axiom**: represents the property that all products are distinct
2. **Szemerédi's bound**: |A||B| < N²/(2 log N)
3. **Limit existence**: questions whether ratio limit exists as N→∞

## References

- Szemerédi (1976)
- Related: Problems 425, 896
