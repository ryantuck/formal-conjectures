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
# Erdős Problem 815

Graph with restricted subgraph has long cycle.

DISPROVED (for k=23)

*Reference:* [erdosproblems.com/815](https://www.erdosproblems.com/815)
-/

open Finset

open scoped Topology Real

namespace Erdos815

/-- Graph with restricted subgraph property -/
@[category research solved, AMS 05]
theorem not_restricted_long_cycle :
    ∃ (k : ℕ), k = 23 ∧
      ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.edgeFinset.card = 2 * n - 2 →
        (∀ (S : Finset (Fin n)), S.card ≤ n / 2 →
          (G.induce ↑S).edgeFinset.card ≤ S.card) →
        ∃ (C : Finset (Fin n)), C.card = k := by
  sorry

end Erdos815
