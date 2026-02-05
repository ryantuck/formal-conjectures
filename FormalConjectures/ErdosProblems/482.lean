/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Defs

/-!
# Erdős Problem 482

Define a sequence where $a_1 = 1$ and $a_{n+1} = \lfloor\sqrt{2}(a_n + 1/2)\rfloor$ for $n \geq 1$.

The core claim is that the difference $a_{2n+1} - 2a_{2n-1}$ is the $n$-th digit in the binary
expansion of $\sqrt{2}$.

The problem asks to find analogous results for $\theta = \sqrt{m}$ (where $m$ is a positive integer)
and other algebraic numbers using similar recursive sequence constructions.

## References
- Erdős and Graham, ErGr80, p. 96
- Graham and Pollak, GrPo70 (original result for $\sqrt{2}$)
- Stoll, St05, St06 (generalizations)
- OEIS sequence A004539
-/

namespace Erdos482

/-- The recursive sequence defined by a₁ = 1 and aₙ₊₁ = ⌊√2(aₙ + 1/2)⌋ -/
noncomputable def grahamPollakSeq : ℕ → ℤ
  | 0 => 0  -- Define a₀ = 0 for convenience
  | 1 => 1
  | n + 1 => ⌊Real.sqrt 2 * (grahamPollakSeq n + 1/2)⌋

/-- The n-th bit in the binary expansion of √2 after the decimal point -/
noncomputable def binaryDigitSqrt2 (n : ℕ) : ℤ :=
  ⌊2^(n+1) * Real.sqrt 2⌋ - 2 * ⌊2^n * Real.sqrt 2⌋

/-- Main theorem: the difference a₂ₙ₊₁ - 2a₂ₙ₋₁ equals the n-th binary digit of √2 -/
theorem grahamPollak_binary_expansion (n : ℕ) (hn : n ≥ 1) :
    grahamPollakSeq (2*n + 1) - 2 * grahamPollakSeq (2*n - 1) = binaryDigitSqrt2 n := by
  sorry

/-- Open problem: generalization to √m for positive integers m -/
theorem exists_analogous_result_for_sqrt (m : ℕ) (hm : m > 0) :
    ∃ (f : ℕ → ℤ) (g : ℕ → ℤ),
      (∀ n, f (n+1) = ⌊Real.sqrt m * (f n + 1/2)⌋) ∧
      (∃ (relation : ℕ → Prop), ∀ n, relation n →
        ∃ (k : ℤ), f (2*n + 1) - k * f (2*n - 1) = g n) := by
  sorry

end Erdos482
