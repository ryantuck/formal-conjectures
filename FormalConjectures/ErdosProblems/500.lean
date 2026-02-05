/-
Copyright (c) 2025 Formal Conjectures. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

/-!
# Erdős Problem 500: 3-Uniform Hypergraph Edges

What is ex₃(n, K₄³), the maximum number of 3-edges on n vertices with no K₄³
(4 vertices with all 4 possible 3-edges)?

## Status
OPEN

Known bounds:
- Upper bound (Razborov): 0.5611666·C(n,3)
- Lower bound (conjectured): (5/9 + o(1))·C(n,3)
-/

namespace Erdos500

noncomputable axiom ex3 (n : ℕ) : ℕ

theorem razborov_upper_bound (n : ℕ) (hn : n ≥ 4) :
    (ex3 n : ℝ) ≤ 0.56117 * (Nat.choose n 3 : ℝ) := by
  sorry

theorem conjectured_lower_bound :
    ∃ (c : ℝ) (hc : c = 5/9),
      ∀ᶠ n in Filter.atTop,
        (ex3 n : ℝ) ≥ c * (Nat.choose n 3 : ℝ) := by
  sorry

end Erdos500
