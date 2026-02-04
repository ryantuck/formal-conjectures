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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 167

*Reference:* [erdosproblems.com/167](https://www.erdosproblems.com/167)

If $G$ is a graph with at most $k$ edge disjoint triangles then can $G$ be made
triangle-free after removing at most $2k$ edges?
-/

namespace Erdos167

open SimpleGraph

/--
A set of triangles in $G$ is edge-disjoint if no two triangles share an edge.
-/
def AreEdgeDisjointTriangles {V : Type*} (G : SimpleGraph V) (S : Set (Finset V)) : Prop :=
  (∀ s ∈ S, G.IsNClique 3 s) ∧
  (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → Disjoint (G.cliqueSet 3 s₁) (G.cliqueSet 3 s₂))

/--
Tuza's Conjecture: If $G$ is a graph with at most $k$ edge disjoint triangles, then
there exists a set of edges $E' \subseteq G.edgeSet$ with $|E'| \leq 2k$ such that
$G \setminus E'$ is triangle-free.
-/
@[category research open, AMS 05]
theorem erdos_167 : answer(sorry) ↔ ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ),
    (∀ (S : Finset (Finset V)), AreEdgeDisjointTriangles G S → S.card ≤ k) →
    ∃ (E' : Finset (Sym2 V)), ↑E' ⊆ G.edgeSet ∧ E'.card ≤ 2 * k ∧ (G.deleteEdges E').CliqueFree 3 := by
  sorry

end Erdos167
