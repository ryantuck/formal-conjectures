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

/-!
# Erdős Problem 150

*Reference:* [erdosproblems.com/150](https://www.erdos.com/150)
-/

namespace Erdos150

open SimpleGraph Finset Real Filter Topology Classical

/--
A set of vertices S is a vertex cut if removing S disconnects the graph.
We assume the graph is connected initially?
Actually, minimal cut definitions usually apply to connected graphs.
However, if G is disconnected, empty set is a cut?
Usually minimal cut means minimal set separating some u, v?
Problem says "whose removal disconnects the graph".
This implies the graph was connected, or just number of components increases.
Usually implies G connected, G-S disconnected.
-/ 
def IsVertexCut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  G.Connected ∧ ¬ (G.induce (S : Set V)ᶜ).Connected

/--
Minimal vertex cut.
-/ 
def IsMinimalVertexCut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  IsVertexCut G S ∧ ∀ x ∈ S, ¬ IsVertexCut G (S.erase x)

/--
c(n) is the maximum number of minimal cuts a graph on n vertices can have.
-/ 
noncomputable def c (n : ℕ) : ℕ :=
  sSup { k | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    k = (univ.filter (IsMinimalVertexCut G)).card }

/--
The conjecture is that $c(n)^{1/n} \to \alpha$ for some $\alpha < 2$.
Bradač [Br24] proved this.
-/ 
@[category research solved, AMS 05]
theorem erdos_150 :
    ∃ α < 2, Tendsto (fun n ↦ (c n : ℝ) ^ (1 / (n : ℝ))) atTop (nhds α) :=
  sorry

end Erdos150
