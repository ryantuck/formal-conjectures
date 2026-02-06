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
# Erdős Problem 789

Estimate h(n) for sum-free with no equal sums.

OPEN

*Reference:* [erdosproblems.com/789](https://www.erdosproblems.com/789)
-/

open Finset

open scoped Topology Real

namespace Erdos789

/-- h(n): maximal sum-free subset with no equal sums -/
noncomputable def h (n : ℕ) : ℕ := sorry

/-- Bounds for h(n) -/
@[category research open, AMS 11]
theorem sum_free_no_equal_sums :
    ∀ (n : ℕ), (n : ℝ) ^ (1/2 : ℝ) ≤ h n ∧
      h n ≤ ((n : ℝ) * Real.log n) ^ (1/3 : ℝ) := by
  sorry

end Erdos789
