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
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Erdős Problem 127

*Reference:* [erdosproblems.com/127](https://www.erdos.com/127)
-/

namespace Erdos127



open SimpleGraph Filter Real Topology Classical



/--

The size of the largest bipartite subgraph of `G`.

This is equivalent to the maximum size of a cut in `G`.

-/

noncomputable def MaxBipartiteEdges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=

  Finset.sup (Finset.univ : Finset (Finset V))

    (fun S => (G.edgeFinset.filter (fun e => Sym2.map (· ∈ S) e = Sym2.mk (True, False))).card)







/--

The Edwards bound for a graph with `m` edges: $m/2 + (\sqrt{8m+1} - 1)/8$.

-/

noncomputable def EdwardsBound (m : ℕ) : ℝ :=

  m / 2 + (Real.sqrt (8 * m + 1) - 1) / 8



/--

`f(m)` is the maximal excess over the Edwards bound that is guaranteed for all graphs with `m` edges.

We define `f(m)` by taking the minimum over all graphs on `Fin (2 * m)` with `m` edges.

The choice of `2 * m` is sufficient because any graph with `m` edges has at most `2 * m` non-isolated vertices,

and adding isolated vertices does not change the max bipartite cut.

-/

noncomputable def f (m : ℕ) : ℝ :=

  (⨅ (G : SimpleGraph (Fin (2 * m))) (_ : DecidableRel G.Adj) (_ : G.edgeFinset.card = m),

    (MaxBipartiteEdges G : ℝ)) - EdwardsBound m


/--
The conjecture asks if there is an infinite sequence $m_i$ such that $f(m_i) \to \infty$.
Alon [Al96] proved this is true.
-/ 
@[category research solved, AMS 05]
theorem erdos_127 : 
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧ Tendsto (fun k ↦ f (m k)) atTop atTop :=
  sorry

end Erdos127
