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
# Erdős Problem 1124

Decomposition of square and circle into congruent parts.

PROVED

*Reference:* [erdosproblems.com/1124](https://www.erdosproblems.com/1124)
-/

open Finset

open scoped Real

namespace Erdos1124

/-- A square and a circle of the same area can be decomposed into a finite number
    of congruent parts. Proved by Laczkovich; can be accomplished using translations only. -/
@[category research solved, AMS 52]
theorem square_circle_decomposition :
    let square := {p : EuclideanSpace ℝ (Fin 2) |
      |p 0| ≤ 1/2 ∧ |p 1| ≤ 1/2}
    let circle := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 / Real.sqrt Real.pi)
    ∃ (n : ℕ) (parts_S parts_C : Fin n → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ i j, i ≠ j → Disjoint (parts_S i) (parts_S j)) ∧
      (∀ i j, i ≠ j → Disjoint (parts_C i) (parts_C j)) ∧
      (⋃ i, parts_S i) = square ∧
      (⋃ i, parts_C i) = circle ∧
      (∀ i, ∃ t : EuclideanSpace ℝ (Fin 2),
        parts_C i = (· + t) '' parts_S i) := by
  sorry

end Erdos1124
