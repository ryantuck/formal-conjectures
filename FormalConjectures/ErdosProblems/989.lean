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
# Erdős Problem 989

Circle discrepancy in the plane.

SOLVED

*Reference:* [erdosproblems.com/989](https://www.erdosproblems.com/989)
-/

open Finset MeasureTheory Filter

open scoped Topology Real

namespace Erdos989

/-- Circle discrepancy function -/
noncomputable def f (A : ℕ → ℝ × ℝ) (r : ℝ) : ℝ := sorry

/-- Circle discrepancy grows without bound -/
@[category research solved, AMS 11]
theorem circle_discrepancy_unbounded :
    ∀ (A : ℕ → ℝ × ℝ),
      Tendsto (f A) atTop atTop := by
  sorry

end Erdos989
