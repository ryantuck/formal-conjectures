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
# Erdős Problem 927

Maximum number of different clique sizes in graphs.

DISPROVED

*Reference:* [erdosproblems.com/927](https://www.erdosproblems.com/927)
-/

open Finset

open scoped Topology Real

namespace Erdos927

variable {α : Type*}

/-- Disproved: bound on number of different clique sizes -/
@[category research solved, AMS 05]
theorem not_clique_sizes_bound :
    ¬ ∀ (G : SimpleGraph α) [Fintype α],
      {k : ℕ | ∃ (K : Finset α), K.card = k ∧ G.IsClique K}.ncard ≤
        Real.sqrt (Fintype.card α) + 1 := by
  sorry

end Erdos927
