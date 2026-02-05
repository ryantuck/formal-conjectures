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
# Erdős Problem 588

Let f_k(n) denote the maximum number of lines containing at least k points among n points
in the plane with no k+1 collinear. Is f_k(n) = o(n²) for k ≥ 4?

OPEN

*Reference:* [erdosproblems.com/588](https://www.erdosproblems.com/588)
-/

open EuclideanSpace Finset

open scoped Topology Real

namespace Erdos588

/-- f_k(n): max lines with ≥ k points in n-point set with no k+1 collinear -/
noncomputable def f_k (k n : ℕ) : ℕ := sorry

/-- For k ≥ 4, f_k(n) = o(n²) -/
@[category research open, AMS 52]
theorem lines_with_k_points_subquadratic (k : ℕ) (hk : k ≥ 4) (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      (f_k k n : ℝ) < ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos588
