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

/-!
# Erdős Problem 102

*Reference:* [erdosproblems.com/102](https://www.erdos.com/102)
-/

namespace Erdos102

open scoped EuclideanGeometry
open Classical

/--
Let $c>0$ and $h_c(n)$ be such that for any $n$ points in $\mathbb{R}^2$ such that there are
$\\geq cn^2$ lines each containing more than three points, there must be some line containing
$h_c(n)$ many points. Estimate $h_c(n)$. Is it true that, for fixed $c>0$, we have
$h_c(n)\\to \infty$?
-/ noncomputable def linesWithMoreThanThreePoints (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (A.powerset.filter (fun (s : Finset (EuclideanSpace ℝ (Fin 2))) ↦
    s.card > 3 ∧ Collinear ℝ (s : Set (EuclideanSpace ℝ (Fin 2))))).card

-- Note: A set of collinear points defines a line. However, we need to count *lines*, not just subsets.
-- The problem statement says "lines each containing more than three points".
-- A line is determined by 2 points.
-- Let L be the set of lines defined by pairs of points in A.
-- We count l ∈ L such that |l ∩ A| > 3.

def lineThrough (p q : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2)))

def linesDeterminedBy (A : Finset (EuclideanSpace ℝ (Fin 2))) : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  { l | ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ l = lineThrough p q }

noncomputable def countHeavyLines (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard { l ∈ linesDeterminedBy A | (A.filter (fun p ↦ p ∈ l)).card > 3 }

noncomputable def maxPointsOnLine (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  sSup { k | ∃ l ∈ linesDeterminedBy A, (A.filter (fun p ↦ p ∈ l)).card = k }

noncomputable def h (c : ℝ) (n : ℕ) : ℕ :=
  sInf { k | ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n →
    (countHeavyLines A : ℝ) ≥ c * (n : ℝ) ^ 2 → maxPointsOnLine A ≥ k }

@[category research open, AMS 52]
theorem erdos_102 : answer(sorry) ↔ ∀ (c : ℝ), 0 < c →
    Filter.Tendsto (fun n ↦ (h c n : ℝ)) Filter.atTop Filter.atTop := by
  sorry

end Erdos102
