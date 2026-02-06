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
# Erdős Problem 863

Sum vs difference constants comparison.

OPEN

*Reference:* [erdosproblems.com/863](https://www.erdosproblems.com/863)
-/

open Finset

open scoped Topology Real

namespace Erdos863

/-- cᵣ for sum -/
noncomputable def c_sum (r : ℕ) : ℝ := sorry

/-- c'ᵣ for difference -/
noncomputable def c_diff (r : ℕ) : ℝ := sorry

/-- Are constants unequal? Is c'ᵣ < cᵣ? -/
@[category research open, AMS 11]
theorem sum_diff_constants (r : ℕ) (hr : r ≥ 2) (answer : Prop) :
    answer ↔ c_diff r ≠ c_sum r ∧ c_diff r < c_sum r := by
  sorry

end Erdos863
