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

/-!
# Erdős Problem 666

For Qₙ (n-dimensional hypercube), does every subgraph with ≥ εn2^(n-1) edges contain C₆?

DISPROVED by Chung (1992) and Brouwer, Dejter, Thomassen (1993)

*Reference:* [erdosproblems.com/666](https://www.erdosproblems.com/666)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos666

/-- n-dimensional hypercube -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin (2^n)) := sorry

/-- Negation: hypercube can be edge-partitioned into C₆-free subgraphs -/
@[category research solved, AMS 05]
theorem not_hypercube_dense_contains_six_cycle :
    ¬ ∃ ε : ℝ, ε > 0 ∧ ∀ (n : ℕ),
      ∀ (G : SimpleGraph (Fin (2^n))),
        (∀ v w, G.Adj v w → (hypercubeGraph n).Adj v w) →
        G.edgeSet.ncard ≥ Nat.floor (ε * n * 2^(n-1)) →
        sorry := by
  sorry

end Erdos666
