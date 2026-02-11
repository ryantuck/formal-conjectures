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
# Erdős Problem 1117

Maximum points on circles for entire functions.

OPEN

*Reference:* [erdosproblems.com/1117](https://www.erdosproblems.com/1117)
-/

open Finset

open scoped Real

namespace Erdos1117

/-- Does there exist a non-monomial entire function f such that
    lim inf_{r→∞} ν(r) = ∞, where ν(r) = #{z : |z|=r, |f(z)| = M(r)}
    is the number of points achieving the maximum modulus on the circle |z| = r? -/
@[category research open, AMS 30]
theorem entire_functions_circle_maxima :
    answer(sorry) ↔
      ∃ (f : ℂ → ℂ), Differentiable ℂ f ∧
        (¬∃ (c : ℂ) (n : ℕ), ∀ z, f z = c * z ^ n) ∧
        Filter.Tendsto
          (fun r : ℝ => Nat.card {z : ℂ | ‖z‖ = r ∧
            ‖f z‖ = ⨆ (w : ℂ) (_ : ‖w‖ = r), ‖f w‖})
          Filter.atTop Filter.atTop := by
  sorry

end Erdos1117
