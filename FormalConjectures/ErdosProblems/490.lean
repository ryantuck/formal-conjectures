/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

/-!
# Erdős Problem 490: Products Distinct

Let A,B ⊆ {1,...,N} such that all products ab (with a ∈ A and b ∈ B) are distinct.
The question asks whether |A||B| ≪ N²/log N.

## Status
PROVED - Szemerédi (1976)

The bound is essentially tight. The example A = [1,N/2] and B = {N/2 < p ≤ N: p prime}
demonstrates near-optimality.

Erdős further asked whether the limit of (|A||B|log N)/N² exists as N→∞.

## References
- Szemerédi (1976)
- Related: Problems 425, 896
-/

namespace Erdos490

noncomputable axiom distinctProducts (A B : Finset ℕ) : Prop

theorem szemerédi_bound (N : ℕ) (A B : Finset ℕ) :
    ∀ (hA : ∀ a ∈ A, a ≤ N) (hB : ∀ b ∈ B, b ≤ N),
    distinctProducts A B →
    (A.card * B.card : ℝ) < (N : ℝ)^2 / (2 * Real.log N) := by
  sorry

theorem product_ratio_limit (N : ℕ) (A B : Finset ℕ) :
    ∃ (lim : ℝ) (hlim : lim ≥ 1),
      Filter.Tendsto (fun (n : ℕ) => ((n : ℝ)^2 / (n : ℝ)) *
        (A.card * B.card : ℝ) / (Real.log n))
      Filter.atTop (nhds lim) := by
  sorry

end Erdos490
