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
# Erdős Problem 1091

Odd cycles with diagonals in K₄-free graphs.

OPEN

*Reference:* [erdosproblems.com/1091](https://www.erdosproblems.com/1091)
-/

open Finset

open scoped Topology Real

namespace Erdos1091

/-- K₄-free graphs with chromatic number 4 contain odd cycles with diagonals -/
@[category research open, AMS 05]
theorem odd_cycles_with_diagonals (answer : Prop) :
    answer ↔ ∀ (G : SimpleGraph (Fin n)),
      G.chromaticNumber = 4 →
      (∀ (K4 : Finset (Fin n)), K4.card = 4 →
        ∃ u ∈ K4, ∃ v ∈ K4, u ≠ v ∧ ¬G.Adj u v) →
      ∃ (C : List (Fin n)), sorry := by
  sorry

end Erdos1091
