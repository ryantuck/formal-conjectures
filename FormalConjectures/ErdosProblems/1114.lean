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
# Erdős Problem 1114

Polynomial roots and derivative zeros.

PROVED

*Reference:* [erdosproblems.com/1114](https://www.erdosproblems.com/1114)
-/

open Finset

open scoped Real

namespace Erdos1114

/-- Polynomials with roots in unit disc have derivative zeros nearby.
    If all roots of P lie in the unit disc, then all roots of P' lie in a slightly larger disc.
    The exact constant depends on the specific result being referenced. -/
@[category research solved, AMS 30]
theorem polynomial_derivative_zeros (P : Polynomial ℂ) (hP : P ≠ 0) :
    (∀ z : ℂ, P.IsRoot z → ‖z‖ ≤ 1) →
    ∀ z : ℂ, Polynomial.derivative P |>.IsRoot z → ‖z‖ ≤ 1 + (1 : ℝ) / P.natDegree := by
  sorry

end Erdos1114
