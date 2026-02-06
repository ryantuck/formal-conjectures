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
# Erdős Problem 771

Maximum subset avoiding all subset sums.

PROVED

*Reference:* [erdosproblems.com/771](https://www.erdosproblems.com/771)
-/

open Finset

open scoped Topology Real

namespace Erdos771

/-- f(n): maximum subset of {1,...,n} avoiding all subset sums -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- f(n) = (1/2 + o(1))n/log n -/
@[category research solved, AMS 11]
theorem subset_sum_avoidance :
    Filter.Tendsto (fun n => (f n : ℝ) / (n / Real.log n))
      Filter.atTop (nhds (1/2 : ℝ)) := by
  sorry

end Erdos771
