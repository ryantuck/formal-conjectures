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
# Erdős Problem 353

Let A ⊆ ℝ² be a measurable set with infinite measure. Must A contain the vertices of an
isosceles trapezoid of area 1?

What about: isosceles triangle, right-angled triangle, cyclic quadrilateral, or polygon
with congruent sides?

PROVED:
- Kovač-Predojević: Any infinite-measure set contains four points on a circle forming a
  cyclic quadrilateral with area 1.
- Koizumi: Any infinite-measure set contains vertices of an isosceles trapezoid, isosceles
  triangle, and right-angled triangle—all with area 1.
- Kovač: The property fails for parallelograms.
- A set of infinite measure exists where all polygons with congruent sides have area < 1.

*Reference:* [erdosproblems.com/353](https://www.erdosproblems.com/353)
-/

open Filter Topology MeasureTheory

namespace Erdos353

variable [MeasureSpace (ℝ × ℝ)]

/-- Kovač-Predojević: Cyclic quadrilaterals with area 1 -/
@[category research solved, AMS 28]
theorem erdos_353_cyclic_quad (A : Set (ℝ × ℝ)) (hA : volume A = ⊤) :
    ∃ p q r s : ℝ × ℝ, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ s ∈ A ∧
      (∃ c : ℝ × ℝ, ∃ rad : ℝ, dist p c = rad ∧ dist q c = rad ∧
        dist r c = rad ∧ dist s c = rad) ∧
      abs ((p.1 - r.1) * (q.2 - s.2) - (q.1 - s.1) * (p.2 - r.2)) / 2 = 1 := by
  sorry

/-- Koizumi: Isosceles trapezoid with area 1 -/
@[category research solved, AMS 28]
theorem erdos_353_isosceles_trapezoid (A : Set (ℝ × ℝ)) (hA : volume A = ⊤) :
    ∃ p q r s : ℝ × ℝ, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ s ∈ A ∧
      dist p q = dist r s ∧  -- equal legs
      abs ((p.1 - r.1) * (q.2 - s.2) - (q.1 - s.1) * (p.2 - r.2)) / 2 = 1 := by
  sorry

/-- Koizumi: Isosceles triangle with area 1 -/
@[category research solved, AMS 28]
theorem erdos_353_isosceles_triangle (A : Set (ℝ × ℝ)) (hA : volume A = ⊤) :
    ∃ p q r : ℝ × ℝ, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧
      dist p q = dist p r ∧
      abs ((q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)) / 2 = 1 := by
  sorry

/-- Koizumi: Right-angled triangle with area 1 -/
@[category research solved, AMS 28]
theorem erdos_353_right_triangle (A : Set (ℝ × ℝ)) (hA : volume A = ⊤) :
    ∃ p q r : ℝ × ℝ, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧
      (q.1 - p.1) * (r.1 - p.1) + (q.2 - p.2) * (r.2 - p.2) = 0 ∧
      abs ((q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)) / 2 = 1 := by
  sorry

/-- Kovač: Parallelograms fail -/
@[category research solved, AMS 28]
theorem erdos_353_parallelogram_fails :
    ∃ A : Set (ℝ × ℝ), volume A = ⊤ ∧
      ¬∃ p q r s : ℝ × ℝ, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ s ∈ A ∧
        q.1 - p.1 = s.1 - r.1 ∧ q.2 - p.2 = s.2 - r.2 ∧
        abs ((p.1 - r.1) * (q.2 - s.2) - (q.1 - s.1) * (p.2 - r.2)) / 2 = 1 := by
  sorry

end Erdos353
