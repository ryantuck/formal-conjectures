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
import Mathlib.Combinatorics.SimpleGraph.Turan

/-!
# Erdős Problem 59

*Reference:* [erdosproblems.com/59](https://www.erdosproblems.com/59)
-/

namespace Erdos59

open SimpleGraph

/--
$\mathrm{ex}(n;G)$ is the maximum number of edges in a graph on $n$ vertices which does
not contain $G$ as a subgraph.
-/
noncomputable def turanNumber (n : ℕ) {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup { k | ∃ (H : SimpleGraph (Fin n)), Nat.card H.edgeSet = k ∧ ¬ ∃ (f : G ↪g H), True }

/--
Is it true that the number of graphs on $n$ vertices which do not contain $G$ is
$$\leq 2^{(1+o(1))\mathrm{ex}(n;G)}?$$

If $G$ is not bipartite the answer is yes, proved by Erdős, Frankl, and Rödl [EFR86].
The answer is no for $G=C_6$, as proved by Morris and Saxton [MoSa16].
-/
@[category research solved, AMS 05]
theorem erdos_59 : answer(False) ↔ ∀ {m : ℕ} (G : SimpleGraph (Fin m)),
    ∀ (ε : ℝ), 0 < ε → ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    let freeGraphs := { H : SimpleGraph (Fin n) | ¬ ∃ (f : G ↪g H), True }
    (Set.ncard freeGraphs : ℝ) ≤ 2 ^ ((1 + ε) * (turanNumber n G : ℝ)) := by
  sorry

/--
Morris and Saxton [MoSa16] disproved the conjecture by showing that for $G=C_6$ there are at least
$2^{(1+c)\mathrm{ex}(n;C_6)}$ such graphs for infinitely many $n$, for some constant $c>0$.
-/
@[category research solved, AMS 05]
theorem erdos_59_disproof : ∃ (c : ℝ), 0 < c ∧
    { n | let freeGraphs := { H : SimpleGraph (Fin n) | ¬ ∃ (f : cycleGraph 6 ↪g H), True }
          (Set.ncard freeGraphs : ℝ) > 2 ^ ((1 + c) * (turanNumber n (cycleGraph 6) : ℝ)) }.Infinite := by
  sorry

end Erdos59