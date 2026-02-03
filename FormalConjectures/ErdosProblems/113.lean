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
import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# Erdős Problem 113

*Reference:* [erdosproblems.com/113](https://www.erdosproblems.com/113)
-/

namespace Erdos113

open SimpleGraph Classical

/--
If $G$ is bipartite then $\mathrm{ex}(n;G)\ll n^{3/2}$ if and only $G$ is $2$-degenerate, that is,
$G$ contains no induced subgraph with minimal degree at least 3.
-/

-- ex(n, G) is the maximum number of edges in a graph on n vertices not containing G as a subgraph.
-- G is 2-degenerate iff every subgraph has a vertex of degree <= 2.

def ContainsSubgraph {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ (f : W ↪ V), ∀ a b, G.Adj a b → H.Adj (f a) (f b)

noncomputable def ex_num (n : ℕ) {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup { m | ∃ (H : SimpleGraph (Fin n)), H.edgeFinset.card = m ∧ ¬ ContainsSubgraph H G }

def IsTwoDegenerate {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ (S : Set V), S.Nonempty → ∃ v, ∃ (h : v ∈ S), (G.induce S).degree ⟨v, h⟩ ≤ 2

@[category research solved, AMS 05]
theorem erdos_113 {V : Type*} [Fintype V] (G : SimpleGraph V) : answer(True) ↔
  (G.Colorable 2 →
    ((fun n ↦ ((ex_num n G) : ℝ) / (n : ℝ)^(3/2 : ℝ)) =o[Filter.atTop] (fun _ ↦ (1 : ℝ))) ↔
    IsTwoDegenerate G) := by
  sorry

end Erdos113