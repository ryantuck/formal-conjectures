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
# Erdős Problem 604

For n distinct points in R², must there exist a point x such that the number of distinct
distances from x to other points satisfies #{d(x,y) : y ∈ A} ≫ n^{1-o(1)}?
Or even ≫ n/√(log n)?

OPEN ($500 reward)

*Reference:* [erdosproblems.com/604](https://www.erdosproblems.com/604)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos604

/-- Pinned distance problem: ∃ point with ≫ n^{1-o(1)} distinct distances -/
@[category research open, AMS 52]
theorem pinned_distance_problem (answer : Prop) :
    answer ↔ ∀ ε > 0, ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (A : Finset (Fin 2 → ℝ)), A.card = n →
        ∃ x ∈ A, (A.image (fun y => dist x y)).card ≥ Nat.floor (c * (n : ℝ) ^ (1 - ε)) := by
  sorry

/-- Stronger conjecture: ≫ n/√(log n) -/
@[category research open, AMS 52]
theorem pinned_distance_strong_conjecture (answer : Prop) :
    answer ↔ ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (A : Finset (Fin 2 → ℝ)), A.card = n →
        ∃ x ∈ A, (A.image (fun y => dist x y)).card ≥
          Nat.floor (c * (n : ℝ) / Real.sqrt (Real.log n)) := by
  sorry

end Erdos604
