# Erdős Problem 483 - Formalization Log

## Problem Statement

Let f(k) denote the minimal value of N such that whenever {1,...,N} is colored with k colors, there exists a monochromatic solution to a+b=c. These values f(k) are known as Schur numbers.

The problem asks to estimate f(k) and specifically determine whether f(k) < c^k holds for some positive constant c.

## Known Results

- f(1) = 2, f(2) = 5, f(3) = 14, f(4) = 45, f(5) = 161
- Lower bound (Ageron et al., 2021): (380)^(k/5) - O(1)
- Upper bound (Whitehead, 1973): ⌊(e - 1/24) k!⌋ - 1

## Formalization Approach

1. **Defined monochromatic sum condition** (`HasMonochromaticSum`):
   - A coloring has this property if there exist a, b, c with the same color where a+b=c

2. **Schur number** (`schurNumber`):
   - Defined as an axiom since constructive definition would require decidability proofs
   - Represents the minimal N for which every k-coloring has a monochromatic sum

3. **Known values** (`schurNumber_values`):
   - States the five known Schur numbers

4. **Main open problem** (`schurNumber_exponential_bound`):
   - Asks whether exponential bound c^k exists

5. **Bounds**:
   - Lower bound theorem using Filter.Eventually for big-O notation
   - Upper bound theorem with factorial expression

## Technical Notes

- Used axiom for schurNumber to avoid decidability complexities
- Type coercions carefully placed to handle ℕ → ℝ conversions
- Filter.atTop used to express asymptotic behavior properly

## References

- Erdős, 1961, 1965
- Ageron et al., 2021
- Whitehead, 1973
