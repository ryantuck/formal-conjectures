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
# Erdős Problem 1121

Circle coverage conjecture.

PROVED

*Reference:* [erdosproblems.com/1121](https://www.erdosproblems.com/1121)
-/

open Finset

open scoped Real

namespace Erdos1121

/-- If C_1, ..., C_n are circles in R^2 with radii r_1, ..., r_n such that
    no line disjoint from all the circles divides them into two non-empty sets,
    then the circles can be covered by a single circle of radius r = r_1 + ... + r_n.
    Proved by Goodman and Goodman. -/
@[category research solved, AMS 52]
theorem circle_coverage :
    ∀ (n : ℕ) (centers : Fin n → EuclideanSpace ℝ (Fin 2)) (radii : Fin n → ℝ),
      (∀ i, 0 < radii i) →
      (∀ (a b : EuclideanSpace ℝ (Fin 2)), a ≠ b →
        ∃ i, ∃ p ∈ Metric.closedBall (centers i) (radii i),
          ∃ q ∈ Metric.closedBall (centers i) (radii i),
            inner (b - a) (p - a) * inner (b - a) (q - a) ≤ 0) →
      ∃ (c : EuclideanSpace ℝ (Fin 2)),
        (⋃ i, Metric.closedBall (centers i) (radii i)) ⊆
          Metric.closedBall c (∑ i, radii i) := by
  sorry

end Erdos1121
