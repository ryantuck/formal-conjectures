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
# Erdős Problem 94

*Reference:* [erdosproblems.com/94](https://www.erdosproblems.com/94)
-/

namespace Erdos94

open scoped EuclideanGeometry

/--
If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon...
-/
def IsConvexPolygon (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Convex ℝ (convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin 2)))) ∧
  ∀ x ∈ A, x ∉ convexHull ℝ (A.erase x : Set (EuclideanSpace ℝ (Fin 2)))

/--
Suppose $n$ points in $\mathbb{R}^2$ determine a convex polygon and the set of distances between
them is $\{u_1,\ldots,u_t\}$. Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs
of points. Then
$$\sum_i f(u_i)^2 \ll n^3.$$
-/
@[category research open, AMS 52]
theorem erdos_94 : answer(sorry) ↔ ∃ (C : ℝ), ∀ (n : ℕ),
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n → IsConvexPolygon A →
    let distances := Finset.image (fun p : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) ↦ dist p.1 p.2) (A.product A)
    let f (d : ℝ) := ((A.product A).filter (fun p ↦ dist p.1 p.2 = d)).card
    (∑ d ∈ distances, (f d : ℝ) ^ 2) ≤ C * (n : ℝ) ^ 3 := by
  sorry

end Erdos94
