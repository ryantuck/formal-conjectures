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
# Erdős Problem 1115

Path growth in entire functions of finite order.

DISPROVED

*Reference:* [erdosproblems.com/1115](https://www.erdosproblems.com/1115)
-/

open Finset

open scoped Topology Real

namespace Erdos1115

/-- For any phi(r) -> infinity, there exists an entire function f of finite order
    with log M(r) << phi(r)(log r)^2 such that no rectifiable path Gamma
    on which f -> infinity satisfies l(r) = o(r).
    Disproved by Gol'dberg and Eremenko (1979). -/
@[category research solved, AMS 30]
theorem path_growth_entire_functions :
    ∀ (φ : ℝ → ℝ), Filter.Tendsto φ Filter.atTop Filter.atTop →
      ∃ (f : ℂ → ℂ), Differentiable ℂ f ∧
        (∀ᶠ r in Filter.atTop,
          Real.log (⨆ (z : ℂ) (_ : ‖z‖ = r), ‖f z‖) ≤
            φ r * (Real.log r) ^ 2) ∧
        ¬∃ (γ : ℝ → ℂ) (hγ : Continuous γ),
          Filter.Tendsto (fun t => ‖f (γ t)‖) Filter.atTop Filter.atTop ∧
          ∃ (pathLength : ℝ → ℝ),
            Filter.Tendsto (fun r => pathLength r / r) Filter.atTop (𝓝 0) := by
  sorry

end Erdos1115
