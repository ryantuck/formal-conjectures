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
# Erdős Problem 652

Does α_k → ∞ for distinct distances from points?

PROVED by Mathialagan: lower bounds established

*Reference:* [erdosproblems.com/652](https://www.erdosproblems.com/652)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos652

/-- α_k for distinct distances -/
noncomputable def α_k (k : ℕ) : ℝ := sorry

/-- α_k → ∞ -/
@[category research solved, AMS 52]
theorem distinct_distances_tends_infinity :
    Filter.Tendsto α_k Filter.atTop Filter.atTop := by
  sorry

end Erdos652
