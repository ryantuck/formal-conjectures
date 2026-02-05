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
# Erdős Problem 391

Let $t(n)$ be the maximum value such that $n! = a_1 \cdots a_n$ with $t(n) = a_1 \leq \cdots \leq a_n$.

Does $\lim t(n)/n = 1/e$?
Does $t(n)/n \leq 1/e - c/\log n$ for infinitely many n?

Alexeev et al. resolved both affirmatively with explicit constant $c_0 = 0.3044\cdots$.

*Reference:* [erdosproblems.com/391](https://www.erdosproblems.com/391)
-/

open Filter Topology BigOperators Real

namespace Erdos391

/-- t(n) is the maximum minimum factor when n! is written as n-fold product -/
noncomputable def t (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset ℕ, S.card = n ∧ S.prod id = n.factorial ∧
    ∀ a ∈ S, k ≤ a}

/-- Alexeev et al.: lim t(n)/n = 1/e -/
@[category research solved, AMS 11]
theorem erdos_391_limit :
    Tendsto (fun n => (t n : ℝ) / n) atTop (𝓝 (1 / exp 1)) := by
  sorry

/-- Alexeev et al.: Upper bound with explicit constant -/
@[category research solved, AMS 11]
theorem erdos_391_upper_bound :
    ∃ c₀ : ℝ, c₀ > 0 ∧ ∃ᶠ n : ℕ in atTop,
      (t n : ℝ) / n ≤ 1 / exp 1 - c₀ / log n := by
  sorry

end Erdos391
