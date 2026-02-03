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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 88

*Reference:* [erdosproblems.com/88](https://www.erdosproblems.com/88)
-/

namespace Erdos88

open SimpleGraph

/--
For any $\epsilon>0$ there exists $\delta=\delta(\epsilon)>0$ such that if $G$ is a graph on $n$
vertices with no independent set or clique of size $\geq \epsilon\log n$ then $G$ contains an
induced subgraph with $m$ edges for all $m\leq \delta n^2$.
-/
@[category research solved, AMS 05]
theorem erdos_88 : answer(True) ↔ ∀ (ε : ℝ), 0 < ε → ∃ (δ : ℝ), 0 < δ ∧
    ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (s : Finset (Fin n)), G.IsClique s → (s.card : ℝ) < ε * Real.log n) →
    (∀ (s : Finset (Fin n)), G.IsIndepSet ↑s → (s.card : ℝ) < ε * Real.log n) →
    ∀ (m : ℕ), (m : ℝ) ≤ δ * (n : ℝ) ^ 2 →
    ∃ (S : Finset (Fin n)), Nat.card (G.induce ↑S).edgeSet = m := by
  sorry

end Erdos88