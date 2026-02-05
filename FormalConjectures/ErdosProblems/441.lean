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

/-!
# Erdős Problem 441

For N ≥ 1, determine the size of the largest subset A ⊆ {1,...,N} such that
lcm(a,b) ≤ N for all a,b ∈ A.

Chen: DISPROVED Erdős' construction - Proved g(N) ~ (9N/8)^(1/2).

Chen-Dai: Refined upper bound g(N) ≤ (9N/8)^(1/2) + O((N/log N)^(1/2) log log N).

*Reference:* [erdosproblems.com/441](https://www.erdosproblems.com/441)
-/

open Filter Topology BigOperators Real

namespace Erdos441

/-- g(N) is the maximum size of subset with bounded lcm -/
noncomputable def g (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 0 < a ∧ a ≤ N) ∧
    ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N}

/-- Chen: Asymptotic formula -/
@[category research solved, AMS 11]
theorem erdos_441_chen :
    Tendsto (fun N : ℕ => (g N : ℝ) / ((9 * N / 8) ^ ((1:ℝ)/2))) atTop (𝓝 1) := by
  sorry

/-- Chen-Dai: Refined upper bound -/
@[category research solved, AMS 11]
theorem erdos_441_chen_dai :
    ∀ᶠ N : ℕ in atTop,
      (g N : ℝ) ≤ (9 * N / 8) ^ ((1:ℝ)/2) +
        100 * ((N / log N) ^ ((1:ℝ)/2)) * log (log N) := by
  sorry

end Erdos441
