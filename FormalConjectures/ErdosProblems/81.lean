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
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Erdős Problem 81

*Reference:* [erdosproblems.com/81](https://www.erdosproblems.com/81)
-/

namespace Erdos81

open SimpleGraph

/--
Let $G$ be a chordal graph on $n$ vertices - that is, $G$ has no induced cycles of length
greater than $3$.
-/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (n : ℕ), n > 3 → ¬ ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = n ∧
    ∀ (v w : V), v ∈ p.support → w ∈ p.support → G.Adj v w → p.edges.Mem s(v, w)

/--
Can the edges of $G$ be partitioned into $n^2/6+O(n)$ many cliques?
-/
@[category research open, AMS 05]
theorem erdos_81 : answer(sorry) ↔ ∃ (C : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G →
    ∃ (S : Finset (Finset (Fin n))),
      (∀ s ∈ S, G.IsClique s) ∧
      (∀ e ∈ G.edgeFinset, ∃! s ∈ S, ∃ x y, e = s(x, y) ∧ x ∈ s ∧ y ∈ s) ∧
      (S.card : ℝ) ≤ (n : ℝ) ^ 2 / 6 + C * n := by
  sorry

end Erdos81