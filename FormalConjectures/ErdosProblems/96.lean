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
import Mathlib.Analysis.Convex.Basic
import Mathlib.Geometry.Euclidean.Basic

/-!
# Erdős Problem 96

*Reference:* [erdosproblems.com/96](https://www.erdosproblems.com/96)
-/

namespace Erdos96

open scoped EuclideanGeometry

/--
If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon then there are $O(n)$ many pairs
which are distance $1$ apart.
-/
def IsConvexPolygon (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Convex ℝ (convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin 2)))) ∧
  ∀ x ∈ A, x ∉ convexHull ℝ (A.erase x : Set (EuclideanSpace ℝ (Fin 2)))

@[category research open, AMS 52]
theorem erdos_96 : answer(sorry) ↔ ∃ (C : ℝ), ∀ (n : ℕ),
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n → IsConvexPolygon A →
    let unitPairs := (A.product A).filter (fun p ↦ dist p.1 p.2 = 1)
    (unitPairs.card : ℝ) ≤ C * n := by
  sorry

end Erdos96
