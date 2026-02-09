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
# Erdős Problem 808

Sum-product on graphs.

DISPROVED

*Reference:* [erdosproblems.com/808](https://www.erdosproblems.com/808)
-/

open Finset

open scoped Topology Real

namespace Erdos808

variable {α : Type*}

/-- Graph sum -/
def graphSum (G : SimpleGraph α) (A : Finset α) : Finset α := sorry

/-- Graph product -/
def graphProduct (G : SimpleGraph α) (A : Finset α) : Finset α := sorry

/-- Disproved sum-product conjecture on graphs -/
@[category research solved, AMS 05]
theorem not_graph_sum_product :
    ¬ ∀ (c : ℝ) (ε : ℝ), c > 0 → ε > 0 →
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
        G.edgeFinset.card ≥ (n : ℝ) ^ (1 + c) →
        max (graphSum G A).card (graphProduct G A).card ≥ A.card ^ (1 + c - ε) := by
  sorry

end Erdos808
