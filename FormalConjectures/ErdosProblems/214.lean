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
# Erdős Problem 214

*Reference:* [erdosproblems.com/214](https://www.erdosproblems.com/214)
-/

open Metric

namespace Erdos214

/--
A set $S \subset \mathbb{R}^2$ avoids distance 1 if no two points in $S$ are at distance 1.
-/
def AvoidsDistanceOne (S : Set (ℝ × ℝ)) : Prop :=
  ∀ p1 ∈ S, ∀ p2 ∈ S, dist p1 p2 ≠ 1

/--
A set $U \subset \mathbb{R}^2$ contains a unit square if there exist four points in $U$
forming a square with side length 1.
-/
def ContainsUnitSquare (U : Set (ℝ × ℝ)) : Prop :=
  ∃ (p1 p2 p3 p4 : ℝ × ℝ), {p1, p2, p3, p4} ⊆ U ∧
    dist p1 p2 = 1 ∧ dist p2 p3 = 1 ∧ dist p3 p4 = 1 ∧ dist p4 p1 = 1 ∧
    dist p1 p3 = Real.sqrt 2 ∧ dist p2 p4 = Real.sqrt 2

/--
Juhász [Ju79] proved that if $S \subset \mathbb{R}^2$ avoids distance 1, then its complement
contains a unit square.

[Ju79] Juhász, R., _Methods for solving some problems in additive number theory_,
Periodica Mathematica Hungarica (1979).
-/
@[category research solved, AMS 52]
theorem erdos_214 : ∀ (S : Set (ℝ × ℝ)), AvoidsDistanceOne S →
    ContainsUnitSquare (Sᶜ) := by
  sorry

/--
Juhász proved more generally that the complement of $S$ contains a congruent copy of any
set of four points.
-/
@[category research solved, AMS 52]
theorem erdos_214.variants.any_four_points (K : Finset (ℝ × ℝ)) (hK : K.card = 4) :
    ∀ (S : Set (ℝ × ℝ)), AvoidsDistanceOne S →
    ∃ (f : (ℝ × ℝ) ≃ᵢ (ℝ × ℝ)), (f '' (K : Set (ℝ × ℝ))) ⊆ Sᶜ := by
  sorry

end Erdos214
