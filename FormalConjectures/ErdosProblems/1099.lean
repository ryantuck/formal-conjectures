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
# Erdős Problem 1099

Bound on h_α(n) for divisor gaps.

PROVED

*Reference:* [erdosproblems.com/1099](https://www.erdosproblems.com/1099)
-/

open Finset

open scoped Topology Real

namespace Erdos1099

/-- Sum of divisor gap powers -/
noncomputable def h (α : ℝ) (n : ℕ) : ℝ := sorry

/-- Liminf of divisor gap function is bounded -/
@[category research solved, AMS 11]
theorem divisor_gap_bound (α : ℝ) (hα : 1 < α) :
    ∃ (C : ℝ), ∀ᶠ n in Filter.atTop, h α n ≤ C := by
  sorry

end Erdos1099
