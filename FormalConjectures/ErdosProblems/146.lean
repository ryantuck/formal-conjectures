/-
Copyright 2025 The Formal Conjectures Authors.

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
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Erdős Problem 146

*Reference:* [erdosproblems.com/146](https://www.erdosproblems.com/146)
-/

namespace Erdos146

open SimpleGraph Finset Real Classical

/--
A graph G is r-degenerate if every induced subgraph has a vertex of degree at most r.
-/
def IsDegenerate {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    ∃ v, ∃ (h : v ∈ S), (G.induce (S : Set V)).degree ⟨v, h⟩ ≤ r

/--
H is a subgraph of G.
-/
def IsSubgraph {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ f : V ↪ W, ∀ x y, H.Adj x y → G.Adj (f x) (f y)

/--
The Turán number ex(n, H) is the maximum number of edges in a graph with n vertices
that does not contain H as a subgraph.
-/
noncomputable def TuranNumber (n : ℕ) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) : ℕ :=
  sSup { m | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    G.edgeFinset.card = m ∧ ¬ IsSubgraph H G }

/--
Erdős and Simonovits conjectured that if H is bipartite and r-degenerate, then
ex(n, H) = O(n^(2 - 1/r)).
-/
@[category research open, AMS 05]
theorem erdos_146 :
    ∀ r ≥ 1, ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      H.IsBipartite → IsDegenerate H r →
      ∃ C > 0, ∀ n, (TuranNumber n H : ℝ) ≤ C * (n : ℝ) ^ (2 - 1 / (r : ℝ)) := by
  sorry

end Erdos146
