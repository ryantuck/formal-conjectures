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
# Erdős Problem 600

Let e(n,r) be the minimum number of edges in an n-vertex graph (where every edge is in
at least one triangle) that guarantees some edge lies in at least r triangles.
For r ≥ 2: (1) Does e(n,r+1) - e(n,r) → ∞? (2) Does e(n,r+1)/e(n,r) → 1?

OPEN

*Reference:* [erdosproblems.com/600](https://www.erdosproblems.com/600)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos600

/-- e(n,r): min edges guaranteeing some edge in ≥ r triangles -/
noncomputable def e (n r : ℕ) : ℕ := sorry

/-- Does e(n, r+1) - e(n, r) → ∞? -/
@[category research open, AMS 05]
theorem e_difference_diverges (r : ℕ) (hr : r ≥ 2) (answer : Prop) :
    answer ↔ Filter.Tendsto (fun n => (e n (r+1) - e n r : ℝ)) Filter.atTop Filter.atTop := by
  sorry

/-- Does e(n, r+1) / e(n, r) → 1? -/
@[category research open, AMS 05]
theorem e_ratio_to_one (r : ℕ) (hr : r ≥ 2) (answer : Prop) :
    answer ↔ Filter.Tendsto (fun n => (e n (r+1) : ℝ) / (e n r : ℝ)) Filter.atTop (nhds 1) := by
  sorry

end Erdos600
