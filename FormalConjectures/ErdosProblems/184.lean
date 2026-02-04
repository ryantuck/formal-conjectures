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

/-!
# Erdős Problem 184

*Reference:* [erdosproblems.com/184](https://www.erdosproblems.com/184)

Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles and edges.
-/

namespace Erdos184

open SimpleGraph Finset Real Classical

/--
A graph is a cycle subgraph if its non-isolated vertices form a cycle of length at least 3.
-/
def IsCycleSubgraph {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  ∃ n ≥ 3, Nonempty (cycleGraph n ≃g H.induce {v | H.degree v > 0})

/--
A graph is a single edge if it has exactly one edge.
-/
def IsSingleEdge {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  H.edgeFinset.card = 1

/--
Erdős and Gallai conjectured that any graph on n vertices can be decomposed into O(n)
edge-disjoint cycles and edges.
-/
@[category research open, AMS 05]
theorem erdos_184 :
    ∃ C > 0, ∀ n, ∀ (G : SimpleGraph (Fin n)),
    ∃ (Decomp : Finset (SimpleGraph (Fin n))),
    (∀ H ∈ Decomp, IsCycleSubgraph H ∨ IsSingleEdge H) ∧
    (∀ H₁ ∈ Decomp, ∀ H₂ ∈ Decomp, H₁ ≠ H₂ → Disjoint H₁.edgeSet H₂.edgeSet) ∧
    (⋃ H ∈ Decomp, H.edgeSet) = G.edgeSet ∧
    (Decomp.card : ℝ) ≤ C * n := by
  sorry

end Erdos184
