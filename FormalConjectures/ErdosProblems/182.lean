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
# Erdős Problem 182

*Reference:* [erdosproblems.com/182](https://www.erdosproblems.com/182)

Let $k\geq 3$. What is the maximum number of edges that a graph on $n$ vertices can contain if it
does not have a $k$-regular subgraph? Is it $\ll n^{1+o(1)}$?
-/

namespace Erdos182

open SimpleGraph Finset Real Classical Asymptotics

/--
A graph G contains a k-regular subgraph if there is a non-empty subset of vertices S
and a k-regular graph on S that is a subgraph of G.
-/
def ContainsKRegularSubgraph {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (S : Finset V) (_ : S.Nonempty), ∃ (H : SimpleGraph S),
    H.IsRegularOfDegree k ∧ ∀ (u v : S), H.Adj u v → G.Adj u.1 v.1

/--
The maximum number of edges in a graph on n vertices without a k-regular subgraph.
-/
noncomputable def MaxEdgesNoKRegular (n k : ℕ) : ℕ :=
  sSup { m | ∃ (G : SimpleGraph (Fin n)), G.edgeFinset.card = m ∧ ¬ ContainsKRegularSubgraph G k }

/--
Erdős and Sauer asked if the maximum number of edges is $n^{1+o(1)}$.
This was confirmed by Janzer and Sudakov [JaSu23], who proved it is $O(n \log \log n)$.
-/
@[category research solved, AMS 05]
theorem erdos_182 :
    answer(True) ↔ ∀ k ≥ 3, ∃ (o : ℕ → ℝ), o =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ᶠ n in Filter.atTop, (MaxEdgesNoKRegular n k : ℝ) ≤ (n : ℝ) ^ (1 + o n) := by
  sorry

/--
The more precise bound proved by Janzer and Sudakov.
-/
@[category research solved, AMS 05]
theorem erdos_182_precise :
    ∀ k ≥ 3, ∃ C > 0, ∀ᶠ n in Filter.atTop, (MaxEdgesNoKRegular n k : ℝ) ≤ C * n * log (log n) := by
  sorry

end Erdos182
