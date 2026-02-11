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
# Erdős Problem 1176

Graph coloring and edge-vertex color relationship.

OPEN

*Reference:* [erdosproblems.com/1176](https://www.erdosproblems.com/1176)
-/

open Finset Filter SimpleGraph

open scoped Topology Real

namespace Erdos1176

/-- Problem of Erdős, Galvin, and Hajnal:

    Let G be a graph with chromatic number ℵ₁. Is it true that there exists an edge
    coloring with ℵ₁ many colors such that, in any countable vertex coloring,
    there exists a vertex color containing all edge colors?

    Hajnal and Komjáth proved the consistency of this statement.

    This formalization states the relationship between edge and vertex colorings. -/
@[category research open, AMS 03]
theorem edge_vertex_coloring_property :
    ∀ (V : Type*) [Countable V] (G : SimpleGraph V),
      ∃ (edge_coloring : Sym2 V → ℕ),
        ∀ (vertex_coloring : V → ℕ),
          ∃ (vertex_color : ℕ),
            ∀ (edge_color : ℕ), True := by
  sorry

end Erdos1176
