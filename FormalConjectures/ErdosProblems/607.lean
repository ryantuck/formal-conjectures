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
# Erdős Problem 607

For n points in the plane, is the number of distinct possible multisets of line-intersection
cardinalities F(n) ≤ exp(O(√n))?

PROVED by Szemerédi and Trotter

*Reference:* [erdosproblems.com/607](https://www.erdosproblems.com/607)
-/

open EuclideanSpace

open scoped Topology Real

namespace Erdos607

/-- F(n): number of distinct line-intersection multisets -/
noncomputable def F (n : ℕ) : ℕ := sorry

/-- F(n) ≤ exp(O(√n)) -/
@[category research solved, AMS 52]
theorem line_multisets_exponential_sqrt :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (F n : ℝ) ≤ Real.exp (c * Real.sqrt n) := by
  sorry

end Erdos607
