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
# Erdős Problem 1174

Graph coloring and monochromatic cliques.

OPEN

*Reference:* [erdosproblems.com/1174](https://www.erdosproblems.com/1174)
-/

open Finset Filter SimpleGraph

open scoped Topology Real

namespace Erdos1174

/-- Problem of Erdős and Hajnal: Two questions about graphs and edge colorings.

    1. Does there exist a graph G with no K₄ such that every edge coloring of G
       with countably many colors contains a monochromatic K₃?

    2. Does there exist a graph G with no K_{ℵ₁} such that every edge coloring of G
       with countably many colors contains a monochromatic K_{ℵ₀}?

    Shelah showed that graphs with either property can consistently exist. -/
@[category research open, AMS 03]
theorem graph_coloring_monochromatic_cliques_question1 :
    ∃ (V : Type*) (G : SimpleGraph V),
      (∀ (K4 : Finset V), K4.card = 4 → ¬G.IsClique (K4 : Set V)) ∧
      (∀ (coloring : Sym2 V → ℕ), True →
        ∃ (K3 : Finset V) (c : ℕ), K3.card = 3 ∧ G.IsClique (K3 : Set V) ∧
          ∀ e ∈ K3.sym2, coloring e = c) := by
  sorry

end Erdos1174
