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
# Erdős Problem 523

For random polynomial f(z)=∑_{k≤n} ε_k z^k where ε_k ∈ {-1,1} are independent uniform,
does max_{|z|=1} |f(z)| = (1+o(1))√(n log n) almost surely?

SOLVED: Halász (1973) proved this with constant C=1.

*Reference:* [erdosproblems.com/523](https://www.erdosproblems.com/523)
-/

open MeasureTheory ProbabilityTheory Real Complex BigOperators Filter Topology

namespace Erdos523

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Random polynomial max on unit circle grows like √(n log n) -/
@[category research solved, AMS 60]
theorem random_polynomial_max_unit_circle
    (eps : ℕ → Ω → Fin 2)
    (h_indep : iIndepFun eps ℙ)
    (h_unif : ∀ k, ℙ {ω | eps k ω = 0} = 1/2 ∧ ℙ {ω | eps k ω = 1} = 1/2) :
    ∀ᵐ ω ∂ℙ,
      Tendsto (fun n =>
        (⨆ (z : ℂ) (hz : ‖z‖ = 1),
          ‖∑ k ∈ Finset.range (n + 1), (if eps k ω = 0 then -1 else 1 : ℝ) * z ^ k‖) /
        Real.sqrt (n * Real.log n)) atTop (𝓝 1) := by
  sorry

end Erdos523
