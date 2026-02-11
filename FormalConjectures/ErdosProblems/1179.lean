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
# Erdős Problem 1179

Estimation of g_ε(N), the minimal subset size for subset sum uniformity.

Let G be an abelian group of size N, A ⊆ G a random subset of size k, and
F_A(g) = #{S ⊆ A : g = ∑_{x∈S} x}. Define g_ε(N) as the minimal k such that
with probability → 1 as N → ∞:
  |F_A(g) - 2^k/N| ≤ ε · 2^k/N  for all g ∈ G.

Main question: Is g_ε(N) = (1 + o(1)) log₂ N for all ε > 0?

PROVED - Erdős-Hall: g_ε(N) ≤ (1 + O(log log log N / log log N)) log₂ N

*Reference:* [erdosproblems.com/1179](https://www.erdosproblems.com/1179)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos1179

/-- For all ε ∈ (0,1), is it true that the minimal subset size g_ε(N) needed
    for subset sum distribution to be ε-close to uniform satisfies
    g_ε(N) = (1 + o(1)) log₂ N?

    Erdős-Hall proved the upper bound g_ε(N) ≤ (1 + O(log log log N / log log N)) log₂ N,
    confirming this is true. -/
@[category research solved, AMS 11]
theorem subset_sum_asymptotic_estimate :
    answer(True) ↔
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ (g_ε : ℕ → ℕ),
          (fun N => (g_ε N : ℝ)) ~[atTop] (fun N => Real.log N / Real.log 2) := by
  sorry

end Erdos1179
