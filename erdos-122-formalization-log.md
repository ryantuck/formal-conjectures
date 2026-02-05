# Erdős Problem 122 Formalization Log

## Problem Statement
For which number theoretic functions f is it true that, for any F(n) satisfying f(n)/F(n) → 0 for almost all n, there exist infinitely many x such that:
#{n ∈ ℕ : n+f(n) ∈ (x, x+F(x))} / F(x) → ∞

## Formalization Approach
- Defined `AlmostAll` predicate to capture the notion of "for almost all n" using density
- Defined `HasShiftedDistributionProperty` to encode the distribution condition
- Formalized the problem as asking for a characterization of which functions satisfy this property

## Key Definitions
1. **AlmostAll**: A property holds for almost all n if the exceptional set has density 0
2. **HasShiftedDistributionProperty**: Encodes the condition about shifted values landing in intervals
3. **erdos_122**: The main problem statement asking for characterization

## Notes
- This is an open research problem
- Erdős, Pomerance, and Sárközy showed it holds for divisor function and count of distinct prime divisors
- Erdős conjectured it fails for Euler's totient φ(n) and sum of divisors σ(n)

## Status
✓ Formalized successfully
✓ Builds without errors
