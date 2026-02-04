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
import FormalConjecturesForMathlib.Combinatorics.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem 163

*Reference:* [erdosproblems.com/163](https://www.erdosproblems.com/163)
-/

namespace Erdos163

open SimpleGraph Combinatorics

/--
The Ramsey number $R(H)$ is the smallest $N$ such that any 2-coloring of the edges of $K_N$
contains a monochromatic copy of $H$.
-/
noncomputable def graphRamsey {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] : ℕ :=
  sInf { N | ∀ (c : Sym2 (Fin N) → Fin 2),
    ∃ (f : V ↪ Fin N) (i : Fin 2), ∀ u v, H.Adj u v → c s(f u, f v) = i }

/--
A graph $G$ is $d$-degenerate if every non-empty subgraph has a vertex of degree at most $d$.
-/
def IsDegenerate {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ (s : Finset V), s.Nonempty → ∃ v, ∃ (h : v ∈ s), (G.induce (s : Set V)).degree ⟨v, h⟩ ≤ d

/--
For any $d \ge 1$ if $H$ is a graph such that every subgraph contains a vertex of degree at most $d$
then $R(H) \ll_d n$.

Solved by Lee [Le17], who proved that $R(H) \leq 2^{2^{O(d)}}n$.

[Le17] C. Lee, _Ramsey numbers of degenerate graphs_, Ann. of Math. (2) 185 (2017), 791–829.
-/
@[category research solved, AMS 05]
theorem erdos_163 : answer(True) ↔ ∀ d ≥ 1, ∃ C : ℝ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj],
    IsDegenerate H d → (graphRamsey H : ℝ) ≤ C * Fintype.card V := by
  sorry

end Erdos163