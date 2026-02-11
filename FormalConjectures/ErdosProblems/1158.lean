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
# Erdős Problem 1158

Turán number for complete multipartite hypergraphs.

OPEN

*Reference:* [erdosproblems.com/1158](https://www.erdosproblems.com/1158)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos1158

/-- Let K_t(r) denote the complete t-partite t-uniform hypergraph with r vertices in each class.
    Conjecture: For all positive integers t and r,
    ex_t(n, K_t(r)) ≥ n^(t - r^(1-t) - o(1))

    Erdős established bounds showing:
    n^(t - O(r^(1-t))) ≤ ex_t(n, K_t(r)) ≪ n^(t - r^(1-t))

    This formulation states the conjectured lower bound asymptotically.

    NOTE: The existential quantifier over ex makes this trivially satisfiable.
    The actual statement should define ex_t as the Turán number and prove the bound. -/
@[category research open, AMS 05]
theorem turan_complete_multipartite_hypergraph_conjecture :
    answer(sorry) ↔
      ∀ (t r : ℕ), t > 0 → r > 0 →
      ∀ (ε : ℝ), ε > 0 →
      ∃ (N : ℕ), ∀ n ≥ N,
        ∃ (ex : ℕ → ℕ), (ex n : ℝ) ≥ (n : ℝ)^((t : ℝ) - (r : ℝ)^(1 - (t : ℝ)) - ε) := by
  sorry

end Erdos1158
