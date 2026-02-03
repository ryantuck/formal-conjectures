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

/-!
# Erdős Problem 80

*Reference:* [erdosproblems.com/80](https://www.erdosproblems.com/80)
-/

namespace Erdos80

open SimpleGraph

/--
A book of size $m$ is an edge shared by at least $m$ different triangles.
-/
def HasBook {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) : Prop :=
  ∃ (u v : V), G.Adj u v ∧ (G.commonNeighbors u v).toFinset.card ≥ m

/--
Let $c>0$ and let $f_c(n)$ be the maximal $m$ such that every graph $G$ with $n$ vertices and at
least $cn^2$ edges, where each edge is contained in at least one triangle, must contain a book
of size $m$.

Estimate $f_c(n)$. In particular, is it true that $f_c(n)>n^{\epsilon}$ for some $\epsilon>0$?
Or $f_c(n)\gg \log n$?
-/
@[category research open, AMS 05]
theorem erdos_80 : answer(sorry) ↔ ∀ (c : ℝ), 0 < c → ∃ (ε : ℝ), 0 < ε ∧
    ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (Nat.card G.edgeSet : ℝ) ≥ c * (n : ℝ) ^ 2 →
    (∀ (u v : Fin n), G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w) →
    ∃ (m : ℕ), (m : ℝ) > (n : ℝ) ^ ε ∧ HasBook G m := by
  sorry

end Erdos80
