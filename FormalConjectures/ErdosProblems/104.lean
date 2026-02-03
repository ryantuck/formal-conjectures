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
# Erdős Problem 104

*Reference:* [erdosproblems.com/104](https://www.erdosproblems.com/104)
-/

namespace Erdos104

open scoped EuclideanGeometry
open Classical

/--
Given $n$ points in $\mathbb{R}^2$ the number of distinct unit circles containing at least three
points is $o(n^2)$.
-/

def IsOnUnitCircle (c : EuclideanSpace ℝ (Fin 2)) (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  dist p c = 1

noncomputable def countUnitCircles (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard { c : EuclideanSpace ℝ (Fin 2) | (A.filter (IsOnUnitCircle c)).card ≥ 3 }

noncomputable def maxUnitCircles (n : ℕ) : ℕ :=
  sSup { k | ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n ∧ countUnitCircles A = k }

@[category research open, AMS 52]
theorem erdos_104 : answer(sorry) ↔
    Filter.Tendsto (fun n ↦ (maxUnitCircles n : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds 0) := by
  sorry

end Erdos104
