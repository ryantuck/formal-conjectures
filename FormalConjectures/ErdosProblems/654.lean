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
# Erdős Problem 654

For n points in ℝ² with no four on a circle, is f(n) > (1-o(1))n or at least > (1/3+c)n?

OPEN (2026 construction disproved strongest form)

*Reference:* [erdosproblems.com/654](https://www.erdosproblems.com/654)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos654

/-- f(n): min distinct distances from some point -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Is f(n) > (1/3+c)n for some c>0? -/
@[category research open, AMS 52]
theorem min_distinct_distances_no_four_cocircular (answer : Prop) :
    answer ↔ ∃ c > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      f n > Nat.floor ((1/3 + c) * n) := by
  sorry

end Erdos654
