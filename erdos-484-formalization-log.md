# Erdős Problem 484 - Formalization Log

## Problem Statement

There exists an absolute constant c > 0 such that whenever {1,...,N} is k-colored (with N sufficiently large), at least cN integers can be expressed as monochromatic sums a+b where a,b have the same color and a ≠ b.

## Status

PROVED by Erdős, Sárközy, and Sós

## Formalization Approach

1. **Defined monochromatic sum property** (`IsMonochromaticSum`):
   - A number is a monochromatic sum if it equals a+b for distinct a,b of the same color

2. **Counting functions** (as axioms):
   - `monochromaticSumsCard`: counts all monochromatic sums
   - `monochromaticSumsEvenCard`: counts even monochromatic sums

3. **Main theorem** (`exists_constant_for_monochromatic_sums`):
   - States existence of constant c > 0 such that every k-coloring has ≥ cN monochromatic sums

4. **Refined bounds**:
   - General k-color bound: N/2 - O(N^(1-1/2^(k+1))) even monochromatic sums
   - Two-color bound: N/2 - O(log N) even monochromatic sums
   - Optimality: O(log N) bound is best possible for 2 colors

## Technical Notes

- Used axioms for counting functions to avoid decidability issues
- Used Filter.atTop and Filter.Eventually for asymptotic statements
- Carefully handled type coercions between ℕ and ℝ

## References

- Erdős, Er61, p.230 (original conjecture of Roth)
- Erdős, Sárközy, and Sós (solution)
