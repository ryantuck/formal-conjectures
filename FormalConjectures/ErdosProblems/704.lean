/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 704

Estimate chromatic number χ(G_n) of unit distance graph in ℝ^n.

OPEN (bounds: (1+o(1))1.2^n ≤ χ(G_n) ≤ (3+o(1))^n)

*Reference:* [erdosproblems.com/704](https://www.erdosproblems.com/704)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos704

/-- Unit distance graph in ℝ^n -/
def unitDistanceGraph (n : ℕ) : SimpleGraph (Fin n → ℝ) := sorry

/-- Chromatic number -/
noncomputable def chromaticNumber {α : Type*} (G : SimpleGraph α) : ℕ := sorry

/-- Bounds for χ(G_n) -/
@[category research open, AMS 05]
theorem unit_distance_chromatic_bounds :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        c₁ ^ n ≤ chromaticNumber (unitDistanceGraph n) ∧
        chromaticNumber (unitDistanceGraph n) ≤ c₂ ^ n := by
  sorry

end Erdos704
