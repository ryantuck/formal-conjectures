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
# Erdős Problem 754

Maximum equidistant points in ℝ⁴.

PROVED

*Reference:* [erdosproblems.com/754](https://www.erdosproblems.com/754)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos754

/-- Maximum number of equidistant points in ℝ⁴ -/
@[category research solved, AMS 52]
theorem max_equidistant_points_four_dim :
    ∀ (S : Finset (Fin 4 → ℝ)) (c : Fin 4 → ℝ),
      (∀ x y : Fin 4 → ℝ, x ∈ S → y ∈ S → x ≠ y →
        dist x c = dist y c) →
      S.card ≤ 5 := by
  sorry

end Erdos754
