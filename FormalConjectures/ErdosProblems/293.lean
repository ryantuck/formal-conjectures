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
# Erdős Problem 293

*Reference:* [erdosproblems.com/293](https://www.erdosproblems.com/293)
-/

open Filter Topology

namespace Erdos293

/--
Let k ≥ 1 and let v(k) be the minimal integer which does not appear as some $n_i$
in a solution to: $1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$ with $1\leq n_1<\cdots <n_k$.

Question: Estimate the growth of v(k).

Known bounds:
- Bleicher and Erdős: $v(k) \gg k!$
- Upper bound: $v(k) \leq kc_0^{2^k}$ where $c_0 \approx 1.26408$ is the Vardi constant
- van Doorn and Tang: $v(k) \geq e^{ck^2}$ for some constant $c > 0$
-/
noncomputable def v (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (a : Fin k → ℕ),
    (∀ i j, i < j → a i < a j) →
    (1 : ℝ) = ∑ i : Fin k, (1 : ℝ) / (a i : ℝ) →
    ∀ i, a i ≠ n}

/--
Bleicher and Erdős: $v(k) \gg k!$.
-/
@[category research solved, AMS 11]
theorem erdos_293.lower_bound_factorial :
    ∃ C > 0, ∀ k : ℕ, k ≥ 1 → (v k : ℝ) ≥ C * (Nat.factorial k : ℝ) := by
  sorry

/--
Upper bound: $v(k) \leq kc_0^{2^k}$ where $c_0 \approx 1.26408$ is the Vardi constant.
-/
@[category research solved, AMS 11]
theorem erdos_293.upper_bound_vardi :
    let c₀ := (1.26408 : ℝ)  -- Vardi constant
    ∀ k : ℕ, k ≥ 1 → (v k : ℝ) ≤ (k : ℝ) * c₀^((2 : ℝ)^k) := by
  sorry

/--
van Doorn and Tang: $v(k) \geq e^{ck^2}$ for some constant $c > 0$.
-/
@[category research solved, AMS 11]
theorem erdos_293.van_doorn_tang :
    ∃ c > 0, ∀ k : ℕ, k ≥ 1 → (v k : ℝ) ≥ Real.exp (c * (k : ℝ)^2) := by
  sorry

/--
Open question: Determine the precise growth rate of v(k).
-/
@[category research open, AMS 11]
theorem erdos_293 :
    ∃ f : ℕ → ℝ, ∀ ε > 0, ∃ K, ∀ k ≥ K,
      (1 - ε) * f k ≤ v k ∧ (v k : ℝ) ≤ (1 + ε) * f k := by
  sorry

end Erdos293
