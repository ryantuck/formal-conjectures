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
# Erdős Problem 105

*Reference:* [erdosproblems.com/105](https://www.erdosproblems.com/105)
-/

namespace Erdos105

open scoped EuclideanGeometry
open Classical

/--
Let $A,B\subset \mathbb{R}^2$ be disjoint sets of size $n$ and $n-3$ respectively, with not all
of $A$ contained on a single line. Is there a line which contains at least two points from $A$
and no points from $B$?
-/

def lineThrough (p q : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2)))

@[category research solved, AMS 52]
theorem erdos_105 : answer(False) ↔ ∃ n, ∃ (A B : Finset (EuclideanSpace ℝ (Fin 2))),
    Disjoint A B ∧ A.card = n ∧ B.card = n - 3 ∧
    ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) ∧
    ∀ p ∈ A, ∀ q ∈ A, p ≠ q →
      ∃ b ∈ B, b ∈ lineThrough p q := by
  sorry

end Erdos105