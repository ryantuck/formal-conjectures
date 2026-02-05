# Erdős Problem 493 - Formalization Log

## Problem Statement

Does there exist k such that every sufficiently large integer n can be expressed as:
∏_{i=1}^k a_i - ∑_{i=1}^k a_i where each a_i ≥ 2?

## Status

PROVED - Eli Seamans with k=2

## Formalization Approach

1. **Product-minus-sum theorem**: proves existence for k=2
2. **Seamans' identity**: explicit formula n = 2(n+2) - (2 + (n+2))
3. **Verified in Lean**: both theorems are proven

## Key Result

Using Seamans' elegant identity: for any n, setting a=2 and b=n+2 gives
2(n+2) - (2 + (n+2)) = 2n + 4 - n - 4 = n

## References

- Schinzel (problem attribution)
- Eli Seamans (solution)
