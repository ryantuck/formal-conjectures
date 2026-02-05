# Erdős Problem 482 - Formalization Log

## Problem Statement

Define a sequence where a₁ = 1 and aₙ₊₁ = ⌊√2(aₙ + 1/2)⌋ for n ≥ 1.

The problem states that the difference a₂ₙ₊₁ - 2a₂ₙ₋₁ equals the n-th digit in the binary expansion of √2.

The open question asks to find analogous results for θ = √m (where m is a positive integer) and other algebraic numbers.

## Formalization Approach

1. **Defined the recursive sequence** (`grahamPollakSeq`):
   - Uses pattern matching with base cases for 0 and 1
   - Recursive case implements ⌊√2(aₙ + 1/2)⌋

2. **Defined binary digit extraction** (`binaryDigitSqrt2`):
   - Extracts the n-th bit from the binary expansion of √2
   - Formula: ⌊2^(n+1) * √2⌋ - 2 * ⌊2^n * √2⌋

3. **Main theorem** (`grahamPollak_binary_expansion`):
   - States the relationship between sequence differences and binary digits
   - Left as `sorry` (proof omitted)

4. **Generalization** (`exists_analogous_result_for_sqrt`):
   - Captures the open problem about generalizations to other square roots
   - Existentially quantified to allow for analogous constructions

## References

- Erdős and Graham, ErGr80, p. 96
- Graham and Pollak, GrPo70 (original result)
- Stoll, St05, St06 (generalizations)
- OEIS sequence A004539

## Notes

- The formalization captures both the specific result for √2 and the open-ended nature of the generalization problem
- Fixed import deprecation warning for `Mathlib.Algebra.Order.Floor`
