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
# Erdős Problem 525: Littlewood's Conjecture

For random polynomials with ±1 coefficients, what is the behavior of
m(f) = min_{|z|=1} |f(z)|?

SOLVED: Kashin (1987) proved Littlewood's conjecture that m(f) = o(1) almost surely.
Konyagin (1994) showed m(f) ≤ n^{-1/2+o(1)} almost surely.

*Reference:* [erdosproblems.com/525](https://www.erdosproblems.com/525)
-/

open MeasureTheory ProbabilityTheory Real Complex BigOperators Filter Topology

namespace Erdos525

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Littlewood's conjecture: minimum on unit circle tends to 0 -/
@[category research solved, AMS 60]
theorem littlewood_minimum_conjecture
    (eps : ℕ → Ω → Fin 2)
    (h_indep : iIndepFun eps ℙ)
    (h_unif : ∀ k, ℙ {ω | eps k ω = 0} = 1/2 ∧ ℙ {ω | eps k ω = 1} = 1/2) :
    ∀ᵐ ω ∂ℙ,
      Tendsto (fun n =>
        ⨅ (z : ℂ) (hz : ‖z‖ = 1),
          ‖∑ k ∈ Finset.range (n + 1), (if eps k ω = 0 then -1 else 1 : ℝ) * z ^ k‖)
        atTop (𝓝 0) := by
  sorry

end Erdos525
