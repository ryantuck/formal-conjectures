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
# Erdős Problem 812

Ramsey number growth rate.

OPEN

*Reference:* [erdosproblems.com/812](https://www.erdosproblems.com/812)
-/

open Finset

open scoped Topology Real

namespace Erdos812

/-- Ramsey number R(n) -/
noncomputable def R (n : ℕ) : ℕ := sorry

/-- R(n+1)/R(n) ≥ 1+c or R(n+1)-R(n) ≫ n² -/
@[category research open, AMS 05]
theorem ramsey_growth_rate (answer : Prop) :
    answer ↔ (∃ c : ℝ, c > 0 ∧
      ∀ (n : ℕ), (R (n + 1) : ℝ) / R n ≥ 1 + c) ∨
      (∃ C : ℝ, C > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, R (n + 1) - R n ≥ C * (n : ℝ) ^ 2) := by
  sorry

end Erdos812
