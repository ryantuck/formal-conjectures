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
# Erdős Problem 1079

Degree and neighborhood conditions.

SOLVED

*Reference:* [erdosproblems.com/1079](https://www.erdosproblems.com/1079)
-/

open Finset

open scoped Topology Real

namespace Erdos1079

/-- Degree and neighborhood conditions in graphs -/
@[category research solved, AMS 05]
theorem degree_neighborhood_condition (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v w : Fin n, G.degree v = G.degree w) →
        ∃ (k : ℕ), ∀ v : Fin n, G.degree v = k := by
  sorry

end Erdos1079
