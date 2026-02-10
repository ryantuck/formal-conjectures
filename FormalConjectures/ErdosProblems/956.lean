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
# Erdős Problem 956

Maximum unit distances between disjoint convex translates.

OPEN

*Reference:* [erdosproblems.com/956](https://www.erdosproblems.com/956)
-/

open Finset

open scoped Topology Real

namespace Erdos956

/-- Maximum unit distance pairs among disjoint convex translates -/
@[category research open, AMS 52]
theorem unit_distance_translates (answer : Prop) :
    answer ↔ ∃ (c : ℝ), 0 < c ∧
      ∀ (n : ℕ), ∃ (C : Set (ℝ × ℝ)) (points : Finset (ℝ × ℝ)),
        IsCompact C ∧ Convex ℝ C ∧ points.card = n ∧
        (∀ p ∈ points, ∀ q ∈ points, p ≠ q →
          Disjoint ({x | ∃ y ∈ C, x = y + p}) ({x | ∃ y ∈ C, x = y + q})) →
        c * (n : ℝ) ^ (1 + c) ≤ {pq : (ℝ × ℝ) × (ℝ × ℝ) |
          pq.1 ∈ points ∧ pq.2 ∈ points ∧ dist pq.1 pq.2 = 1}.ncard := by
  sorry

end Erdos956
