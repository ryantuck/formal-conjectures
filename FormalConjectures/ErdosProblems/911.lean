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
# Erdős Problem 911

Size Ramsey number growth.

OPEN

*Reference:* [erdosproblems.com/911](https://www.erdosproblems.com/911)
-/

open Finset

open scoped Topology Real

namespace Erdos911

/-- Size Ramsey number -/
noncomputable def sizeRamsey (G : SimpleGraph α) : ℕ := sorry

/-- Function f with f(x)/x → ∞ and Ramsey number > f(C)e -/
@[category research open, AMS 05]
theorem size_ramsey_growth (answer : Prop) :
    answer ↔ ∃ (f : ℕ → ℝ),
      Filter.Tendsto (fun x => f x / x) Filter.atTop Filter.atTop ∧
      sorry := by
  sorry

end Erdos911
