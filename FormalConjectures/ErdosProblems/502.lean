/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

/-!
# Erdős Problem 502: Two Distances in Sets

What is the largest A ⊆ ℝⁿ with only two distinct distances between its elements?

## Status
SOLVED

Result (Bannai, Bannai & Stanton, 1983): |A| ≤ C(n+2, 2)
Further work: Petrov & Pohoata (2021), Alweiss (construction)
-/

namespace Erdos502

noncomputable def twoDistanceSet (n : ℕ) (A : Set (Fin n → ℝ)) : Prop :=
  ∃ (d₁ d₂ : ℝ), d₁ ≠ d₂ ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
    (∃ (i : Fin n), (a i - b i) ^ 2 = d₁) ∨ (∃ (i : Fin n), (a i - b i) ^ 2 = d₂)

theorem two_distance_bound (n : ℕ) (A : Set (Fin n → ℝ))
    (h : twoDistanceSet n A) (hA : A.Finite) :
    hA.toFinset.card ≤ Nat.choose (n + 2) 2 := by
  sorry

end Erdos502
