/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

/-!
# Erdős Problem 484: Monochromatic Sums in Colorings

There exists an absolute constant c > 0 such that whenever {1,...,N} is k-colored (with N
sufficiently large depending on k), at least cN integers in this set are representable as
monochromatic sums—that is, each can be expressed as a+b where a,b ∈ {1,...,N} belong to the
same color class and a ≠ b.

## Status
PROVED - Erdős, Sárközy, and Sós established that at least N/2 - O(N^(1-1/2^(k+1))) even numbers
have this property. For the two-color case, they proved at least N/2 - O(log N) even numbers work,
with O(log N) shown to be optimal.

## References
- Erdős, Er61, p.230 (original conjecture of Roth)
- Erdős, Sárközy, and Sós (solution)
-/

namespace Erdos484

/-- A number n is a monochromatic sum in coloring if n = a + b for some a ≠ b
    with the same color -/
def IsMonochromaticSum (N k : ℕ) (coloring : Fin N → Fin k) (n : ℕ) : Prop :=
  ∃ (a b : Fin N), a ≠ b ∧ a.val + b.val = n ∧ coloring a = coloring b

/-- Count of monochromatic sums for a given coloring -/
axiom monochromaticSumsCard (N k : ℕ) (coloring : Fin N → Fin k) : ℕ

/-- Main theorem: there exists a constant c such that every k-coloring has
    at least cN monochromatic sums -/
theorem exists_constant_for_monochromatic_sums (k : ℕ) :
    ∃ (c : ℝ) (hc : c > 0),
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ∀ (coloring : Fin N → Fin k),
          (monochromaticSumsCard N k coloring : ℝ) ≥ c * N := by
  sorry

/-- Count of even monochromatic sums -/
axiom monochromaticSumsEvenCard (N k : ℕ) (coloring : Fin N → Fin k) : ℕ

/-- For k colors, at least N/2 - O(N^(1-1/2^(k+1))) even numbers are monochromatic sums -/
theorem monochromatic_sums_bound (k : ℕ) :
    ∃ (C : ℝ),
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ∀ (coloring : Fin N → Fin k),
          (monochromaticSumsEvenCard N k coloring : ℝ) ≥
            (N : ℝ) / 2 - C * (N : ℝ)^(1 - 1 / 2^(k+1)) := by
  sorry

/-- For 2 colors, at least N/2 - O(log N) even numbers are monochromatic sums -/
theorem monochromatic_sums_two_colors :
    ∃ (C : ℝ),
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ∀ (coloring : Fin N → Fin 2),
          (monochromaticSumsEvenCard N 2 coloring : ℝ) ≥
            (N : ℝ) / 2 - C * Real.log N := by
  sorry

/-- The O(log N) bound for 2 colors is optimal -/
theorem two_color_bound_optimal :
    ∃ (coloring : (N : ℕ) → Fin N → Fin 2),
      ∀ (C : ℝ),
        ∃ᶠ (N : ℕ) in Filter.atTop,
          (monochromaticSumsEvenCard N 2 (coloring N) : ℝ) ≤
            (N : ℝ) / 2 - C * Real.log N := by
  sorry

end Erdos484
