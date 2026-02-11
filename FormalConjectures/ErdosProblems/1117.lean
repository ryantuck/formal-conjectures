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

/-- Maximum points on circles for entire functions.
    Asks about properties of where entire functions achieve their maximum modulus on circles.
    The current formalization is a placeholder. -/
@[category research open, AMS 30]
theorem entire_functions_circle_maxima :
    ∀ (f : ℂ → ℂ) (r : ℝ), 0 < r →
      ∃ (z : ℂ), ‖z‖ = r ∧
        (∀ w : ℂ, ‖w‖ = r → ‖f z‖ ≥ ‖f w‖) ∧ -- z is a maximum on the circle
        True := by -- Additional property about such maxima
  sorry

end Erdos1117
