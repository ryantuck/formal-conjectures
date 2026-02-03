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
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Erdős Problem 111

*Reference:* [erdosproblems.com/111](https://www.erdosproblems.com/111)
-/

namespace Erdos111

open SimpleGraph Classical

/--
If $G$ is a graph let $h_G(n)$ be defined such that any subgraph of $G$ on $n$ vertices can be
made bipartite after deleting at most $h_G(n)$ edges.
What is the behaviour of $h_G(n)$? Is it true that $h_G(n)/n\to \infty$ for every graph $G$
with chromatic number $\aleph_1$?
-/ 

def CanBeMadeBipartiteByDeletingEdges {V : Type*} (H : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (E' : Set (Sym2 V)), E' ⊆ H.edgeSet ∧ E'.ncard ≤ k ∧ (H.deleteEdges E').Colorable 2

noncomputable def h_G {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sInf { k | ∀ (S : Set V), S.ncard = n → CanBeMadeBipartiteByDeletingEdges (G.induce S) k }

@[category research open, AMS 05]
theorem erdos_111 : answer(sorry) ↔
  ∀ (V : Type) (G : SimpleGraph V), G.chromaticNumber = Cardinal.aleph 1 →
    Filter.Tendsto (fun n ↦ (h_G G n : ℝ) / n) Filter.atTop Filter.atTop := by
  sorry

end Erdos111
