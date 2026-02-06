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
# Erdős Problem 742

Diameter 2 graph edge bound.

RESOLVED (DECIDABLE - proved for large n)

*Reference:* [erdosproblems.com/742](https://www.erdosproblems.com/742)
-/

open Finset

open scoped Topology Real

namespace Erdos742

variable {α : Type*}

/-- Graph diameter -/
noncomputable def diameter (G : SimpleGraph α) : ℕ∞ := sorry

/-- Diameter 2 graphs have at most n^2/4 edges -/
@[category research solved, AMS 05]
theorem diameter_two_edge_bound :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        diameter G = 2 →
        (∀ e : Sym2 (Fin n), e ∈ G.edgeSet →
          diameter (G.deleteEdges {e}) > 2) →
        G.edgeFinset.card ≤ n ^ 2 / 4 := by
  sorry

end Erdos742
