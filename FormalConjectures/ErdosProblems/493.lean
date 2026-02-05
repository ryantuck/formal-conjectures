/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

/-!
# Erdős Problem 493: Product Minus Sum

Does there exist a constant k such that every sufficiently large integer can be expressed as:

∏_{i=1}^k a_i - ∑_{i=1}^k a_i

where each a_i ≥ 2?

## Status
PROVED - Eli Seamans showed k=2 works using: n = 2(n+2) - (2 + (n+2))

The solution suggests Schinzel's original formulation may have had additional constraints.
-/

namespace Erdos493

theorem product_minus_sum_k2 (n : ℕ) :
    ∃ (a b : ℕ), a ≥ 2 ∧ b ≥ 2 ∧ (a * b : ℤ) - (a + b) = n := by
  use 2, n + 2
  simp only [Nat.cast_add, Nat.cast_ofNat]
  norm_num
  ring

theorem seamans_identity (n : ℕ) :
    (n : ℤ) = 2 * (n + 2) - (2 + (n + 2)) := by
  ring

end Erdos493
