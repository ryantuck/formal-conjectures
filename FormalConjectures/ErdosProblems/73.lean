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
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 73

*Reference:* [erdosproblems.com/73](https://www.erdosproblems.com/73)
-/

namespace Erdos73

open SimpleGraph

/--
Let $k\geq 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent set of
size $\geq (n-k)/2$, where $n$ is the number of vertices of $H$. Must $G$ be the union of a
bipartite graph and $O_k(1)$ many vertices?
-/
@[category research solved, AMS 05]
theorem erdos_73 : answer(True) ↔ ∀ (k : ℕ), ∃ (C : ℕ), ∀ (V : Type*) (G : SimpleGraph V),
    (∀ (V' : Finset V), ∃ (S : Finset V), S ⊆ V' ∧ G.IsIndepSet ↑S ∧
      (S.card : ℝ) ≥ (V'.card - k : ℝ) / 2) →
    ∃ (S : Finset V), S.card ≤ C ∧ (G.induce (Set.univ \ ↑S)).IsBipartite := by
  sorry

end Erdos73