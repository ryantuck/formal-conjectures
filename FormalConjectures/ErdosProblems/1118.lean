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
# Erdős Problem 1118

Growth rate of entire functions with finite measure level sets.

SOLVED

*Reference:* [erdosproblems.com/1118](https://www.erdosproblems.com/1118)
-/

open Finset MeasureTheory

open scoped Real

namespace Erdos1118

/-- If f is a non-constant entire function and E(c) = {z : |f(z)| > c}
    has finite planar measure for some c, then
    ∫ r in [0, ∞), r / log(log(M(r))) < ∞ where M(r) = sup_{|z|=r} |f(z)|.
    Proved by Camera (1977) and Gol'dberg (1979). -/
@[category research solved, AMS 30]
theorem entire_function_level_set_measure (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hnc : ¬∀ z, f z = f 0) :
    ∀ c : ℝ,
      volume {z : ℂ | c < ‖f z‖} < ⊤ →
        ∫ (r : ℝ) in Set.Ioi 0,
          r / Real.log (Real.log (⨆ (z : ℂ) (_ : ‖z‖ = r), ‖f z‖)) < ⊤ := by
  sorry

end Erdos1118
