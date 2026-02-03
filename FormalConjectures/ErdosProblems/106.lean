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
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Erdős Problem 106

*Reference:* [erdosproblems.com/106](https://www.erdosproblems.com/106)
-/

namespace Erdos106

open scoped EuclideanGeometry
open Classical MeasureTheory

/--
Draw $n$ squares inside the unit square with no common interior point. Let $f(n)$ be the
maximum possible sum of the side-lengths of the squares. Is $f(k^2+1)=k$?
-/

structure AxisAlignedSquare where
  center : EuclideanSpace ℝ (Fin 2)
  side : ℝ
  side_pos : 0 < side

def squareSet (s : AxisAlignedSquare) : Set (EuclideanSpace ℝ (Fin 2)) :=
  { p | |p 0 - s.center 0| ≤ s.side / 2 ∧ |p 1 - s.center 1| ≤ s.side / 2 }

def squareInterior (s : AxisAlignedSquare) : Set (EuclideanSpace ℝ (Fin 2)) :=
  { p | |p 0 - s.center 0| < s.side / 2 ∧ |p 1 - s.center 1| < s.side / 2 }

def UnitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  { p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 }

def InsideUnitSquare (S : List AxisAlignedSquare) : Prop :=
  ∀ s ∈ S, squareSet s ⊆ UnitSquare

def NoCommonInterior (S : List AxisAlignedSquare) : Prop :=
  S.Pairwise (fun s1 s2 ↦ squareInterior s1 ∩ squareInterior s2 = ∅)

noncomputable def f (n : ℕ) : ℝ :=
  sSup { l | ∃ (S : List AxisAlignedSquare), S.length = n ∧ InsideUnitSquare S ∧ NoCommonInterior S ∧ (S.map (·.side)).sum = l }

@[category research open, AMS 52]
theorem erdos_106 : answer(sorry) ↔ ∀ k : ℕ, f (k^2 + 1) = k := by
  sorry

end Erdos106