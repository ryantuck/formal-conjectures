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
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Erdős Problem 98

*Reference:* [erdosproblems.com/98](https://www.erdos.com/98)
-/

namespace Erdos98

open scoped EuclideanGeometry

/--
Let $h(n)$ be such that any $n$ points in $\mathbb{R}^2$, with no three on a line and no four on
a circle, determine at least $h(n)$ distinct distances. Does $h(n)/n\to \infty$?
-/  
def InGeneralPosition (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ s ⊆ A, s.card = 3 → ¬ Collinear ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))) ∧
  (∀ s ⊆ A, s.card = 4 → ¬ EuclideanGeometry.Concyclic (s : Set (EuclideanSpace ℝ (Fin 2))))

noncomputable def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (Finset.image (fun p : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) ↦ dist p.1 p.2)
    (A.product A)).card

noncomputable def h (n : ℕ) : ℕ :=
  sInf { k | ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n ∧ InGeneralPosition A ∧ distinctDistances A = k }

@[category research open, AMS 52]
theorem erdos_98 : answer(sorry) ↔ Filter.Tendsto (fun n ↦ (h n : ℝ) / n) Filter.atTop Filter.atTop :=
  sorry

end Erdos98
