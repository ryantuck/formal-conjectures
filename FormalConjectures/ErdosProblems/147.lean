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
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Erdős Problem 147

*Reference:* [erdosproblems.com/147](https://www.erdosproblems.com/147)
-/

namespace Erdos147

open SimpleGraph Finset Real Classical

/--
H is a subgraph of G.
-/
def IsSubgraph {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ f : V ↪ W, ∀ x y, H.Adj x y → G.Adj (f x) (f y)

/--
The Turán number ex(n, H).
-/
noncomputable def TuranNumber (n : ℕ) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) : ℕ :=
  sSup { m | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    G.edgeFinset.card = m ∧ ¬ IsSubgraph H G }

/--
Minimum degree of H.
-/
def MinDegree {V : Type*} [Fintype V] [Nonempty V] (H : SimpleGraph V) [DecidableRel H.Adj] : ℕ :=
  univ.inf' univ_nonempty (fun v => H.degree v)

/--
The conjecture is that if H is bipartite with min degree r, then ex(n, H) >> n^(2 - 1/(r-1) + ε).
Disproved by Janzer [Ja23].
-/
@[category research solved, AMS 05]
theorem erdos_147 :
    answer(False) ↔ ∀ r ≥ 2, ∀ {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      H.IsBipartite → MinDegree H ≥ r →
      ∃ ε > 0, ∃ C > 0, ∀ n, (TuranNumber n H : ℝ) ≥ C * (n : ℝ) ^ (2 - 1 / ((r : ℝ) - 1) + ε) := by
  sorry

end Erdos147
