/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 529

Let d_k(n) be the expected distance from origin after n random steps in ℤ^k
for self-avoiding walks. Does lim d_2(n)/√n = ∞? Is d_k(n) ≪ √n for k ≥ 3?

OPEN with partial results for k ≥ 5 (Hara & Slade).

*Reference:* [erdosproblems.com/529](https://www.erdosproblems.com/529)
-/

open Real Filter

namespace Erdos529

/-- Expected distance for self-avoiding walks -/
noncomputable def expectedDistance (n k : ℕ) : ℝ := sorry

/-- Expected distance grows faster than √n for k=2 -/
@[category research open, AMS 82]
theorem saw_distance_k2_superlinear :
    Tendsto (fun n => expectedDistance n 2 / Real.sqrt n) atTop atTop := by
  sorry

/-- Expected distance is O(√n) for k ≥ 3 -/
@[category research open, AMS 82]
theorem saw_distance_high_dim_bounded (k : ℕ) (hk : k ≥ 3) :
    ∃ C > 0, ∀ n : ℕ, expectedDistance n k ≤ C * Real.sqrt n := by
  sorry

end Erdos529
