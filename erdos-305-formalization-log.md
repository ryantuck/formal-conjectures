# Erdős Problem 305 Formalization Log

## Problem Statement
For integers 1 ≤ a < b, let D(a,b) denote the minimal value of n_k such that there exist integers 1 ≤ n₁ < ... < n_k with a/b = 1/n₁ + ... + 1/n_k. Estimate D(b) = max D(a,b).

## Formalization Approach
- Defined `UnitFractionRep` to represent a rational as a sum of distinct unit fractions
- Defined `D_ab` as the minimal largest denominator in such a representation
- Defined `D` as the maximum over all valid a < b
- Formalized the known bounds as separate theorems

## Key Definitions
1. **UnitFractionRep**: A list of distinct positive integers whose reciprocals sum to a/b
2. **D_ab**: The minimal largest denominator needed
3. **D**: The worst case over all proper fractions with denominator b

## Theorems Formalized
- Bleicher-Erdős: D(b) = O(b(log b)²)
- Yokota (1988): Improved to O(b log b (log log b)⁴ (log log log b)²)
- Liu-Sawhney (2024): Further improved to O(b log b (log log b)³)
- Lower bound for primes: D(p) = Ω(p log p)

## Status
✓ Formalized successfully
✓ Builds without errors
