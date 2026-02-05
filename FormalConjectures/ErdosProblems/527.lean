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
# Erdős Problem 527

Given a_n ∈ ℝ where ∑|a_n|² = ∞ and |a_n| = o(1/√n), does there exist z with |z| = 1
such that ∑ ε_n a_n z^n converges for almost all choices of signs ε_n = ±1?

SOLVED: Michelen-Sawhney (2025) proved affirmatively.

*Reference:* [erdosproblems.com/527](https://www.erdosproblems.com/527)
-/

open MeasureTheory ProbabilityTheory Real Complex Filter BigOperators Topology

namespace Erdos527

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Random sign series convergence on unit circle -/
@[category research solved, AMS 60]
theorem random_sign_convergence :
    ∀ (a : ℕ → ℝ), (¬Summable fun n => (a n) ^ 2) →
      (∀ ε > 0, ∃ N, ∀ n ≥ N, |a n| < ε / Real.sqrt n) →
      ∀ (eps : ℕ → Ω → Fin 2), iIndepFun eps ℙ →
      (∀ k, ℙ {ω | eps k ω = 0} = 1/2 ∧ ℙ {ω | eps k ω = 1} = 1/2) →
      ∀ᵐ ω ∂ℙ,
        ∃ (z : ℂ), ‖z‖ = 1 ∧
          ∃ L : ℂ, Tendsto (fun n => ∑ k ∈ Finset.range n,
            (if eps k ω = 0 then -1 else 1 : ℝ) * a k * z ^ k) atTop (𝓝 L) := by
  sorry

end Erdos527
