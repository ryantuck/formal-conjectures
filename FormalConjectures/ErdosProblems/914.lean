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
# Erdős Problem 914

Vertex-disjoint cliques in dense graphs.

PROVED

*Reference:* [erdosproblems.com/914](https://www.erdosproblems.com/914)
-/

open Finset

open scoped Topology Real

namespace Erdos914

variable {α : Type*}

/-- Every graph with rm vertices and minimum degree ≥ m(r-1) contains m vertex disjoint K_r -/
@[category research solved, AMS 5]
theorem vertex_disjoint_cliques (r m : ℕ) :
    ∀ (G : SimpleGraph (Fin (r * m))) [DecidableRel G.Adj],
      (∀ v : Fin (r * m), m * (r - 1) ≤ G.degree v) →
      ∃ (cliques : Finset (Finset (Fin (r * m)))),
        cliques.card = m ∧
        (∀ C ∈ cliques, C.card = r ∧ G.IsClique (C : Set (Fin (r * m)))) ∧
        (∀ C₁ ∈ cliques, ∀ C₂ ∈ cliques, C₁ ≠ C₂ → Disjoint C₁ C₂) := by
  sorry

end Erdos914
