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
# Erdős Problem 988

Discrepancy on unit sphere.

SOLVED

*Reference:* [erdosproblems.com/988](https://www.erdosproblems.com/988)
-/

open Finset MeasureTheory

open scoped Topology Real

namespace Erdos988

/-- Minimum discrepancy tends to infinity -/
@[category research solved, AMS 11]
theorem sphere_discrepancy_unbounded (d : ℕ) :
    ∀ (D : Finset (EuclideanSpace ℝ (Fin d)) → ℝ),
      Tendsto (fun n => sInf {D P | P.card = n ∧ ∀ p ∈ P, ‖p‖ = 1})
        atTop atTop := by
  sorry

end Erdos988
