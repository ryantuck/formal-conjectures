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
# Erdős Problem 1088

Minimal points with distinct distances.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1088](https://www.erdosproblems.com/1088)
-/

open Finset

open scoped Topology Real

namespace Erdos1088

/-- English version: Minimal point sets with distinct distances -/@[category research open, AMS 52]
theorem minimal_distinct_distances (n : ℕ) :
    ∃ (m : ℕ), ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      S.card = m →
      sorry := by
  sorry

end Erdos1088
