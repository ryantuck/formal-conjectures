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
# Erdős Problem 969

Squarefree integer error term.

OPEN

*Reference:* [erdosproblems.com/969](https://www.erdosproblems.com/969)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos969

/-- Count of squarefree integers up to x -/
noncomputable def Q (x : ℝ) : ℝ := sorry

/-- Error term in squarefree counting function -/
@[category research open, AMS 11]
theorem squarefree_error_term (answer : ℝ → ℝ) :
    ∃ (E : ℝ → ℝ),
      (∀ x > 0, Q x = 6 / Real.pi ^ 2 * x + E x) ∧
      sorry := by
  sorry

end Erdos969
