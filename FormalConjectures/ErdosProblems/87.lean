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
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 87

*Reference:* [erdosproblems.com/87](https://www.erdosproblems.com/87)
-/

namespace Erdos87

open Combinatorics SimpleGraph

/--
The Ramsey number $R(G)$ is the smallest $N$ such that any 2-coloring of the edges of $K_N$
contains a monochromatic copy of $G$.
-/
noncomputable def graphRamsey {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { N | ∀ (c : Sym2 (Fin N) → Fin 2),
    ∃ (f : V ↪ Fin N) (i : Fin 2), ∀ u v, G.Adj u v → c s(f u, f v) = i }

/--
Let $\epsilon >0$. Is it true that, if $k$ is sufficiently large, then
$$R(G)>(1-\epsilon)^kR(k)$$
for every graph $G$ with chromatic number $\chi(G)=k$?
-/
@[category research open, AMS 05]
theorem erdos_87 : answer(sorry) ↔ ∀ (ε : ℝ), 0 < ε → ∃ (k₀ : ℕ), ∀ (k : ℕ), k₀ ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.chromaticNumber = k →
    (graphRamsey G : ℝ) > (1 - ε) ^ k * (hypergraphRamsey 2 k : ℝ) := by
  sorry

/--
Even stronger, is there some $c>0$ such that, for all large $k$, $R(G)>cR(k)$ for every graph
$G$ with chromatic number $\chi(G)=k$?
-/
@[category research open, AMS 05]
theorem erdos_87_strong : answer(sorry) ↔ ∃ (c : ℝ), 0 < c ∧ ∃ (k₀ : ℕ), ∀ (k : ℕ), k₀ ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.chromaticNumber = k →
    (graphRamsey G : ℝ) > c * (hypergraphRamsey 2 k : ℝ) := by
  sorry

end Erdos87
