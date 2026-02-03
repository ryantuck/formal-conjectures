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
# Erdős Problem 93

*Reference:* [erdosproblems.com/93](https://www.erdos.com/93)
-/

namespace Erdos93

open scoped EuclideanGeometry

/--
If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon then they determine at least
$\lfloor \frac{n}{2}\rfloor$ distinct distances.
-/ 
def IsConvexPolygon (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Convex ℝ (convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin 2)))) ∧
  ∀ x ∈ A, x ∉ convexHull ℝ (A.erase x : Set (EuclideanSpace ℝ (Fin 2)))

noncomputable def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (Finset.image (fun p : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) ↦ dist p.1 p.2)
    (A.product A)).card

@[category research open, AMS 52]
theorem erdos_93 : answer(sorry) ↔ ∀ (n : ℕ),
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n → IsConvexPolygon A →
    distinctDistances A ≥ n / 2 := by
  sorry

end Erdos93
