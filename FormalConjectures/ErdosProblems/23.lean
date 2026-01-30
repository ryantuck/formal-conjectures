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
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 23

*Reference:* [erdosproblems.com/23](https://www.erdosproblems.com/23)
-/

namespace Erdos23

open SimpleGraph

/--
Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?

This problem is open.
-/
@[category research open, AMS 05]
theorem erdos_23 : answer(sorry) ↔ ∀ n : ℕ, ∀ (G : SimpleGraph (Fin (5 * n))),
    G.CliqueFree 3 →
    ∃ (E : Set (Sym2 (Fin (5 * n)))),
      E ⊆ G.edgeSet ∧
      E.ncard ≤ n ^ 2 ∧
      (G.deleteEdges E).IsBipartite := by
  sorry

end Erdos23
