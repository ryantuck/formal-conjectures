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
# Erdős Problem 655

For n points in ℝ² with no circle centered at any x_i containing three other points,
are there at least (1+c)n/2 distinct distances?

OPEN (counterexample using equally-spaced points on circle found)

*Reference:* [erdosproblems.com/655](https://www.erdosproblems.com/655)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos655

/-- At least (1+c)n/2 distinct distances with circle constraint -/
@[category research open, AMS 52]
theorem distinct_distances_circle_constraint (answer : Prop) :
    answer ↔ ∃ c > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (A : Finset (Fin 2 → ℝ)), A.card = n →
        (∀ x ∈ A, sorry) →
        sorry ≥ Nat.floor ((1 + c) * n / 2) := by
  sorry

end Erdos655
