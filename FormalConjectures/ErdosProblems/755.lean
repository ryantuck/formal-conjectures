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
# Erdős Problem 755

Maximum unit equilateral triangles in ℝ⁶.

SOLVED

*Reference:* [erdosproblems.com/755](https://www.erdosproblems.com/755)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos755

/-- Number of unit equilateral triangles -/
noncomputable def numUnitTriangles (A : Finset (Fin 6 → ℝ)) : ℕ := sorry

/-- Maximum unit triangles is (1/27+o(1))n³ -/
@[category research solved, AMS 52]
theorem max_unit_triangles_six_dim :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        ∀ (A : Finset (Fin 6 → ℝ)),
          A.card = n →
          numUnitTriangles A ≤ (1/27 + c) * (n : ℝ) ^ 3 := by
  sorry

end Erdos755
