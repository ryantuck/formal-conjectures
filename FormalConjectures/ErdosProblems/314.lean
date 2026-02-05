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
# Erdős Problem 314

For $n \geq 1$, let $m$ be the minimal integer such that $\sum_{n \leq k \leq m} \frac{1}{k} \geq 1$.
Define the overshoot $\epsilon(n) = \sum_{n \leq k \leq m} \frac{1}{k} - 1$.

Is it true that $\liminf n^2 \epsilon(n) = 0$?

Lim and Steinerberger proved this affirmatively, showing that for any $\delta > 0$,
there exist infinitely many $n$ with $n^2 |\sum 1/k - 1| \ll 1/(\log n)^{5/4-\delta}$.

*Reference:* [erdosproblems.com/314](https://www.erdosproblems.com/314)
-/

open Filter Topology BigOperators Real

namespace Erdos314

/-- The minimal m such that the harmonic sum from n to m is at least 1 -/
noncomputable def m_of (n : ℕ) : ℕ :=
  sInf {m : ℕ | m ≥ n ∧ (Finset.Ico n (m + 1)).sum (fun k => (1 : ℝ) / k) ≥ 1}

/-- The overshoot when the harmonic sum exceeds 1 -/
noncomputable def ε (n : ℕ) : ℝ :=
  (Finset.Ico n (m_of n + 1)).sum (fun k => (1 : ℝ) / k) - 1

/-- Lim-Steinerberger: liminf n² ε(n) = 0 -/
@[category research solved, AMS 11]
theorem erdos_314_liminf_zero :
    ∀ δ > 0, ∃ᶠ n : ℕ in atTop, (n : ℝ)^2 * |ε n| < δ := by
  sorry

/-- Lim-Steinerberger: Explicit upper bound -/
@[category research solved, AMS 11]
theorem erdos_314_lim_steinerberger :
    ∀ δ > 0, ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
      (n : ℝ)^2 * |ε n| ≤ C / (log (n : ℝ))^((5:ℝ)/4 - δ) := by
  sorry

end Erdos314
