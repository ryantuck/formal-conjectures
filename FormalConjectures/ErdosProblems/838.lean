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
# Erdős Problem 838

Distinct convex subsets from n points.

OPEN

*Reference:* [erdosproblems.com/838](https://www.erdosproblems.com/838)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos838

/-- f(n): minimum distinct convex subsets from n points -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Does lim log f(n)/(log n)² exist? -/
@[category research open, AMS 52]
theorem convex_subsets_limit (answer : Prop) :
    answer ↔ ∃ c : ℝ, Filter.Tendsto
      (fun n => Real.log (f n) / (Real.log n) ^ 2)
      Filter.atTop (nhds c) := by
  sorry

end Erdos838
