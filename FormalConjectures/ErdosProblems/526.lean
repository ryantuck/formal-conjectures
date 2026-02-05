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
# Erdős Problem 526

Let a_n ≥ 0 with a_n → 0 and ∑ a_n = ∞. Find necessary and sufficient conditions
such that random arcs of length a_n on the unit circle cover it with probability 1.

SOLVED: Shepp (1972) proved the condition is ∑_n e^{a_1+...+a_n}/n² = ∞.

*Reference:* [erdosproblems.com/526](https://www.erdosproblems.com/526)
-/

open MeasureTheory ProbabilityTheory Real Filter BigOperators Topology

namespace Erdos526

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Shepp's condition for random circle covering -/
@[category research solved, AMS 60]
theorem shepp_circle_covering
    (a : ℕ → ℝ)
    (ha_pos : ∀ n, a n ≥ 0)
    (ha_zero : Tendsto a atTop (𝓝 0))
    (ha_sum : ¬Summable a) :
    (∃ (theta : ℕ → Ω → ℝ), iIndepFun theta ℙ ∧
      (∀ n, ∀ᵐ ω ∂ℙ, theta n ω ∈ Set.Icc 0 (2 * π)) ∧
      ∀ᵐ ω ∂ℙ, ∀ x ∈ Set.Icc (0:ℝ) (2 * π),
        ∃ n, x ∈ Set.Ioo (theta n ω) (theta n ω + a n)) ↔
    (¬Summable fun n => Real.exp (∑ k ∈ Finset.range (n + 1), a k) / (n + 1) ^ 2) := by
  sorry

end Erdos526
