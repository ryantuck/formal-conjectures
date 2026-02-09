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
# Erdős Problem 827

Minimal n_k for k points with distinct circle radii.

OPEN

*Reference:* [erdosproblems.com/827](https://www.erdosproblems.com/827)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos827

/-- n_k: minimal n such that n points determine k with distinct circle radii -/
noncomputable def n_k (k : ℕ) : ℕ := sorry

/-- Determine n_k -/
@[category research open, AMS 52]
theorem distinct_circle_radii :
    ∀ (k : ℕ), n_k k ≥ k + 2 := by
  sorry

end Erdos827
