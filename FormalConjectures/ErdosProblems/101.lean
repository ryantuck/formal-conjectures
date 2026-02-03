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
# Erdős Problem 101

*Reference:* [erdosproblems.com/101](https://www.erdosproblems.com/101)
-/

namespace Erdos101

open scoped EuclideanGeometry
open Classical

/--
Given $n$ points in $\mathbb{R}^2$, no five of which are on a line, the number of lines
containing four points is $o(n^2)$.
-/
def NoFiveOnLine (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ s ⊆ A, s.card = 5 → ¬ Collinear ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))

noncomputable def linesWithFourPoints (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (A.powerset.filter (fun (s : Finset (EuclideanSpace ℝ (Fin 2))) ↦ s.card = 4 ∧ Collinear ℝ (s : Set (EuclideanSpace ℝ (Fin 2))))).card

noncomputable def maxLinesWithFourPoints (n : ℕ) : ℕ :=
  sSup { k | ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n ∧ NoFiveOnLine A ∧ linesWithFourPoints A = k }

@[category research open, AMS 52]
theorem erdos_101 : answer(sorry) ↔
    Filter.Tendsto (fun n ↦ (maxLinesWithFourPoints n : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds 0) := by
  sorry

end Erdos101