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
# Erdős Problem 134

*Reference:* [erdosproblems.com/134](https://www.erdosproblems.com/134)
-/

namespace Erdos134

open SimpleGraph Finset Real Classical

/--
G has diameter 2.
-/
def HasDiameterTwo {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ u v, u ≠ v → G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

/--
The maximum degree of the graph G.
-/
def MaxDegree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  univ.sup (fun v => G.degree v)

/--
The problem asks if a triangle-free graph with max degree $< n^{1/2 - \epsilon}$
can be made into a triangle-free graph with diameter 2 by adding at most $\delta n^2$ edges.
Alon proved this is true.
-/
@[category research solved, AMS 05]
theorem erdos_134 :
    ∀ ε > 0, ∀ δ > 0, ∃ N, ∀ n ≥ N,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.CliqueFree 3 → (MaxDegree G : ℝ) < (n : ℝ) ^ (1 / 2 - ε) →
          ∃ (G' : SimpleGraph (Fin n)) (_ : DecidableRel G'.Adj),
            G ≤ G' ∧ G'.CliqueFree 3 ∧ HasDiameterTwo G' ∧
            ((G'.edgeFinset \ G.edgeFinset).card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  sorry

end Erdos134
