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
# Erdős Problem 1087

Degenerate sets of four points.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1087](https://www.erdosproblems.com/1087)
-/

open Finset

open scoped Topology Real

namespace Erdos1087

/-- English version: Degenerate sets of four points -/@[category research open, AMS 52]
theorem degenerate_four_points (n : ℕ) :
    ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      S.card = n →
      ∃ (T : Finset (EuclideanSpace ℝ (Fin 2))), T ⊆ S ∧ T.card = 4 ∧ sorry := by
  sorry

end Erdos1087
