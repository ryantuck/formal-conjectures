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
# Erdős Problem 311

Let $\delta(N)$ represent the smallest non-zero value of $|1 - \sum 1/n|$ where the sum ranges
over all subsets $A$ of $\{1, \ldots, N\}$.

Is $\delta(N) = e^{-(c+o(1))N}$ for some constant $c \in (0,1)$?

Trivial lower bound: $\delta(N) \geq 1/\text{lcm}(1,\ldots,N) = e^{-(1+o(1))N}$.
Tang established upper bound: $\delta(N) \leq \exp(-cN/(\log N \log \log N)^3)$.

*Reference:* [erdosproblems.com/311](https://www.erdosproblems.com/311)
-/

open Filter Topology BigOperators Real

namespace Erdos311

/-- The smallest non-zero distance from 1 among unit fraction sums -/
noncomputable def δ (N : ℕ) : ℝ :=
  sInf {r : ℝ | r > 0 ∧ ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n ∧ n ≤ N) ∧
    |(1 : ℝ) - A.sum (fun n => (1 : ℝ) / n)| = r}

/-- Trivial lower bound using lcm -/
@[category research solved, AMS 11]
theorem erdos_311_lower_bound :
    ∃ ε : ℕ → ℝ, (∀ᶠ N in atTop, ε N ≥ 0) ∧ (Tendsto ε atTop (𝓝 0)) ∧
      ∀ᶠ N in atTop, δ N ≥ exp (-(1 + ε N) * N) := by
  sorry

/-- Tang's upper bound -/
@[category research solved, AMS 11]
theorem erdos_311_tang_upper :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
      δ N ≤ exp (-c * N / (log N * log (log N))^3) := by
  sorry

/-- The original conjecture asks if δ(N) = exp(-(c+o(1))N) for c ∈ (0,1) -/
def erdos_311_conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∃ ε : ℕ → ℝ, (Tendsto ε atTop (𝓝 0)) ∧
      (∀ᶠ N in atTop, exp (-(c + ε N) * (N : ℝ)) ≤ δ N ∧
        δ N ≤ exp (-(c - ε N) * (N : ℝ)))

end Erdos311
