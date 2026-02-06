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
# Erdős Problem 668

Does the number of incongruent sets of n points in ℝ² maximizing unit distances
tend to infinity as n→∞? Is it always >1 for n>3?

OPEN (uniqueness for 5 ≤ n ≤ 21 by computation)

*Reference:* [erdosproblems.com/668](https://www.erdosproblems.com/668)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos668

/-- Number of incongruent unit-distance-maximizing configurations -/
noncomputable def numMaxConfigs (n : ℕ) : ℕ := sorry

/-- Does numMaxConfigs(n) → ∞? -/
@[category research open, AMS 52]
theorem max_unit_distance_configs_tends_infinity (answer : Prop) :
    answer ↔ Filter.Tendsto numMaxConfigs Filter.atTop Filter.atTop := by
  sorry

end Erdos668
