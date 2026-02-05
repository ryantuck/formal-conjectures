/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Pigeonhole

/-!
# Erdős Problem 483: Schur Numbers

Let f(k) denote the minimal value of N such that whenever {1,...,N} is colored with k colors,
there exists a monochromatic solution to a+b=c.

The problem asks to estimate f(k) and specifically determine whether f(k) < c^k holds for some
positive constant c.

## Known Results
- f(1) = 2, f(2) = 5, f(3) = 14, f(4) = 45, f(5) = 161
- Lower bound (Ageron et al., 2021): (380)^(k/5) - O(1)
- Upper bound (Whitehead, 1973): ⌊(e - 1/24) k!⌋ - 1

## References
- Erdős, 1961, 1965
- Ageron et al., 2021
- Whitehead, 1973
-/

namespace Erdos483

/-- A coloring has a monochromatic sum if there exist a, b, c with the same color
    and a + b = c -/
def HasMonochromaticSum (N k : ℕ) (coloring : Fin N → Fin k) : Prop :=
  ∃ (a b c : Fin N), a.val + b.val = c.val ∧ coloring a = coloring b ∧ coloring b = coloring c

/-- The Schur number f(k) is the minimal N such that every k-coloring of {1,...,N}
    has a monochromatic solution to a+b=c -/
axiom schurNumber (k : ℕ) : ℕ

/-- Known values of small Schur numbers -/
theorem schurNumber_values :
    schurNumber 1 = 2 ∧
    schurNumber 2 = 5 ∧
    schurNumber 3 = 14 ∧
    schurNumber 4 = 45 ∧
    schurNumber 5 = 161 := by
  sorry

/-- Main open problem: Does there exist a constant c such that f(k) < c^k? -/
theorem schurNumber_exponential_bound :
    ∃ (c : ℝ) (hc : c > 0), ∀ k : ℕ, (schurNumber k : ℝ) < c ^ k := by
  sorry

/-- Lower bound from Ageron et al. (2021): f(k) ≥ 380^(k/5) - O(1) -/
theorem schurNumber_lower_bound :
    ∀ᶠ (k : ℕ) in Filter.atTop, (380 : ℝ) ^ ((k : ℝ) / 5) - (k : ℝ) ≤ (schurNumber k : ℝ) := by
  sorry

/-- Upper bound from Whitehead (1973): f(k) ≤ ⌊(e - 1/24) k!⌋ - 1 -/
theorem schurNumber_upper_bound (k : ℕ) :
    (schurNumber k : ℤ) ≤ ⌊(Real.exp 1 - 1/24) * (k.factorial : ℝ)⌋ - 1 := by
  sorry

end Erdos483
