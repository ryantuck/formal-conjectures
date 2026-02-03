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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 133

*Reference:* [erdosproblems.com/133](https://www.erdosproblems.com/133)
-/

namespace Erdos133

open SimpleGraph Finset Real Filter Topology Classical

/--
G has diameter 2. This means any two distinct vertices are at distance at most 2.
Since G is triangle-free (assumed in context), it implies they are not all at distance 1
-/ 
def HasDiameterTwo {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ u v, u ≠ v → G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

/--

The maximum degree of the graph G.

-/

def MaxDegree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=

  univ.sup (fun v => G.degree v)



/--

`f(n)` is the minimal maximum degree of a triangle-free graph with `n` vertices and diameter 2.

-/

noncomputable def f (n : ℕ) : ℕ :=

  sInf { d | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),

    G.CliqueFree 3 ∧ HasDiameterTwo G ∧ MaxDegree G = d }



/--

The problem asks if $f(n)/\sqrt{n} \to \infty$.

This is false. Constructions show $f(n) \le (\frac{2}{\sqrt{3}} + o(1))\sqrt{n}$.

-/

@[category research solved, AMS 05]

theorem erdos_133 :


    answer(False) ↔ Tendsto (fun n ↦ (f n : ℝ) / Real.sqrt n) atTop atTop :=
  sorry

end Erdos133
