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
# Erdős Problem 777

Graphs from comparable subsets.

SOLVED

*Reference:* [erdosproblems.com/777](https://www.erdosproblems.com/777)
-/

open Finset

open scoped Topology Real

namespace Erdos777

/-- First question answered affirmatively -/
@[category research solved, AMS 05]
theorem comparable_subsets_first :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∀ (u v : Fin n), G.Adj u v ↔
        ∃ (A B : Finset (Fin n)), u ∈ A ∧ v ∈ B ∧ A ⊆ B := by
  sorry

/-- Second question answered negatively -/
@[category research solved, AMS 05]
theorem comparable_subsets_second :
    ∃ (P : Prop), ¬P := by
  sorry

end Erdos777
