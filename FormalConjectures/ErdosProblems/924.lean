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
# Erdős Problem 924

Graph coloring and monochromatic cliques.

PROVED

*Reference:* [erdosproblems.com/924](https://www.erdosproblems.com/924)
-/

open Finset

open scoped Topology Real

namespace Erdos924

variable {α : Type*}

/-- Ramsey-type result for graph colorings -/
@[category research solved, AMS 05]
theorem coloring_monochromatic_cliques (k r : ℕ) :
    ∃ (n : ℕ), ∀ (G : SimpleGraph (Fin n)) (c : Fin n → Fin r),
      ∃ (K : Finset (Fin n)),
        K.card = k ∧ G.IsClique K ∧
        (∀ v w : Fin n, v ∈ K → w ∈ K → c v = c w) := by
  sorry

end Erdos924
