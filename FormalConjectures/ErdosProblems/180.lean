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

/-!
# Erdős Problem 180

*Reference:* [erdosproblems.com/180](https://www.erdosproblems.com/180)

If $\mathcal{F}$ is a finite set of finite graphs then $\mathrm{ex}(n;\mathcal{F})$ is the maximum
number of edges a graph on $n$ vertices can have without containing any subgraphs from
$\mathcal{F}$.

Is it true that, for every $\mathcal{F}$, there exists $G\in\mathcal{F}$ such that
$\mathrm{ex}(n;G)\ll_{\mathcal{F}}\mathrm{ex}(n;\mathcal{F})$?

This is false as stated, with a counterexample provided by Zach Hunter: if $\mathcal{F}=\{H_1,H_2\}$
where $H_1$ is a star and $H_2$ is a matching, both with at least two edges, then
$\mathrm{ex}(n;\mathcal{F})\ll 1$, but $\mathrm{ex}(n;H_i)\asymp n$.
-/

namespace Erdos180

open SimpleGraph Finset Real Classical

/--
The Turán number ex(n, H) is the maximum number of edges in a graph with n vertices
that does not contain H as a subgraph.
-/
noncomputable def TuranNumber (n : ℕ) {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  sSup { m | ∃ (G : SimpleGraph (Fin n)), G.edgeFinset.card = m ∧ ¬ Nonempty (H ↪g G) }

/--
The Turán number ex(n, F) for a family of graphs F is the maximum number of edges
in a graph with n vertices that does not contain any H from F as a subgraph.
-/
noncomputable def TuranNumberFamily (n : ℕ) (I : Type) [Fintype I]
    (F : I → Σ V : Type, SimpleGraph V) [∀ i, Fintype (F i).1] : ℕ :=
  sSup { m | ∃ (G : SimpleGraph (Fin n)), G.edgeFinset.card = m ∧ ∀ i, ¬ Nonempty ((F i).2 ↪g G) }

/--
Erdős and Simonovits asked if for every finite family F of finite graphs, there exists G in F
such that ex(n, G) = O(ex(n, F)).
Note that ex(n, F) ≤ ex(n, G) is trivial.

This is false as stated (see Hunter's counterexample).
-/
@[category research open, AMS 05]
theorem erdos_180 :
    answer(False) ↔
    ∀ (I : Type) [Fintype I] (F : I → Σ V : Type, SimpleGraph V) [∀ i, Fintype (F i).1],
    ∃ i : I, ∃ C > 0, ∀ n, (TuranNumber n (F i).2 : ℝ) ≤ C * (TuranNumberFamily n I F : ℝ) := by
  sorry

end Erdos180
