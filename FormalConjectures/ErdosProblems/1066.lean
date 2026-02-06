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
# Erdős Problem 1066

Independent sets in unit distance graphs.

OPEN

*Reference:* [erdosproblems.com/1066](https://www.erdosproblems.com/1066)
-/

open Finset

open scoped Topology Real

namespace Erdos1066

/-- Independent set size in unit distance graph -/
@[category research open, AMS 05]
theorem unit_distance_independent_set (n : ℕ) :
    ∃ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      S.card = n ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≠ 1) ∧
      sorry := by
  sorry

end Erdos1066
