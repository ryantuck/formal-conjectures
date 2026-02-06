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
# Erdős Problem 1127

Decomposition of ℝⁿ into sets with distinct pairwise distances.

SOLVED

*Reference:* [erdosproblems.com/1127](https://www.erdosproblems.com/1127)
-/

open Finset

open scoped Topology Real

namespace Erdos1127

/-- Decomposition of Euclidean space into sets with distinct pairwise distances -/
@[category research solved, AMS 52]
theorem euclidean_space_distinct_distance_decomposition (n : ℕ) (answer : Prop) :
    answer ↔ ∃ (partition : ℕ → Set (EuclideanSpace ℝ (Fin n))),
      (∀ i j, i ≠ j → Disjoint (partition i) (partition j)) ∧
      (⋃ i, partition i) = Set.univ ∧
      (∀ i, ∀ x ∈ partition i, ∀ y ∈ partition i, ∀ z ∈ partition i,
        x ≠ y → y ≠ z → x ≠ z → dist x y ≠ dist y z) := by
  sorry

end Erdos1127
