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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 22

*Reference:* [erdosproblems.com/22](https://www.erdosproblems.com/22)
-/

namespace Erdos22

open SimpleGraph Finset
open scoped Classical

/--
The independence number of a graph.
-/
noncomputable def independenceNumber {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ s, G.IsIndepSet s ∧ k = s.ncard}

/--
Let $\epsilon > 0$ and $n$ be sufficiently large depending on $\epsilon$. Is there a graph on $n$
vertices with $\geq n^2/8$ many edges which contains no $K_4$ such that the largest independent
set has size at most $\epsilon n$?

Solved by Fox, Loh, and Zhao [FLZ15] in the affirmative.

[FLZ15] J. Fox, P. Loh, and Y. Zhao, _The critical window for the classical Ramsey-Turán problem_,
Combinatorica 35 (2015), 435–461.
-/
@[category research solved, AMS 05]
theorem erdos_22 : answer(True) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ (G : SimpleGraph (Fin n)),
    G.CliqueFree 4 ∧
    G.edgeSet.ncard ≥ n^2 / 8 ∧
    (independenceNumber G : ℝ) ≤ ε * n := by
  sorry

end Erdos22
