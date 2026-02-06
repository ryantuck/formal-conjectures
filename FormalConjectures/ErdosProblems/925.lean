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
# Erdős Problem 925

Independent sets in non-Ramsey graphs.

DISPROVED

*Reference:* [erdosproblems.com/925](https://www.erdosproblems.com/925)
-/

open Finset

open scoped Topology Real

namespace Erdos925

variable {α : Type*}

/-- Disproved: large independent sets in non-Ramsey graphs -/
@[category research solved, AMS 05]
theorem not_independent_ramsey :
    ¬ ∀ (k : ℕ) (G : SimpleGraph α) [Fintype α],
      G.CliqueFree k → (G.compl).CliqueFree k →
      ∃ (S : Finset α), G.IsIndepSet S ∧
        Real.log (Fintype.card α) ≤ S.card := by
  sorry

end Erdos925
