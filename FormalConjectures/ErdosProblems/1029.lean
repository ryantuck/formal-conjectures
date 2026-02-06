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
# Erdős Problem 1029

Ramsey numbers growth rate.

OPEN

*Reference:* [erdosproblems.com/1029](https://www.erdosproblems.com/1029)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1029

/-- Diagonal Ramsey number -/
noncomputable def R (k : ℕ) : ℕ := sorry

/-- Ramsey number growth faster than exponential -/
@[category research open, AMS 05]
theorem ramsey_growth_unbounded (answer : Prop) :
    answer ↔ Filter.Tendsto (fun k => (R k : ℝ) / (k * 2 ^ (k / 2))) atTop atTop := by
  sorry

end Erdos1029
