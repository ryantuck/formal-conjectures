/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

/-!
# Erdős Problem 492: Uniform Distribution with Gaps

Given an infinite set A = {a₁ < a₂ < ...} where a_{i+1}/a_i → 1, define
f(x) = (x - a_i)/(a_{i+1} - a_i) ∈ [0,1) for x ∈ [a_i, a_{i+1}).

Is it true that for almost all α, the sequence f(αn) is uniformly distributed in [0,1)?

## Status
Disproved - Schmidt (1969) showed the conjecture does not hold for all sequences.

Originally posed by Le Veque, with partial results by Davenport-LeVeque and Davenport-Erdős.
-/

namespace Erdos492

noncomputable axiom gapSequence (f : ℕ → ℕ) : Prop
noncomputable axiom fractionalPartFunction (f : ℕ → ℕ) (α : ℝ) : ℕ → ℝ

theorem schmidt_counterexample :
    ∃ (f : ℕ → ℕ), gapSequence f ∧
      ∃ (α : ℝ), ¬∀ (ε : ℝ), ε > 0 → ∀ᶠ (k : ℕ) in Filter.atTop,
        |((Finset.range k).card : ℝ) / k - 1/2| < ε := by
  sorry

end Erdos492
