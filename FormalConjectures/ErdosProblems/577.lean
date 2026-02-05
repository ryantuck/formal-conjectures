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
# Erdős Problem 577

If G is a graph on 4k vertices with minimum degree at least 2k, then G contains
k vertex-disjoint 4-cycles.

PROVED by Wang (2010)

*Reference:* [erdosproblems.com/577](https://www.erdosproblems.com/577)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos577

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- A graph on 4k vertices with min degree ≥ 2k has k vertex-disjoint 4-cycles -/
@[category research solved, AMS 05]
theorem vertex_disjoint_four_cycles (k : ℕ) (G : SimpleGraph α) [DecidableRel G.Adj]
    (hcard : Fintype.card α = 4 * k)
    (hmin : ∀ v, G.degree v ≥ 2 * k) :
    ∃ (cycles : Finset (Finset α)),
      cycles.card = k ∧
      (∀ C ∈ cycles, C.card = 4 ∧ ∃ (w : G.Walk (C.min' sorry) (C.min' sorry)),
        w.IsPath ∧ w.length = 4) ∧
      (∀ C₁ C₂, C₁ ∈ cycles → C₂ ∈ cycles → C₁ ≠ C₂ → Disjoint C₁ C₂) := by
  sorry

end Erdos577
