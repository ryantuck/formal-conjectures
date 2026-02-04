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
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Erdős Problem 217

*Reference:* [erdosproblems.com/217](https://www.erdosproblems.com/217)
-/

open EuclideanGeometry

namespace Erdos217

/--
No four points in `A` are concyclic.
-/
def NoFourConcyclic (A : Set ℝ²) : Prop :=
  ∀ s ⊆ A, s.ncard = 4 → ¬ Concyclic s

/--
The set of distances determined by a finite set of points.
-/
noncomputable def Distances (A : Finset ℝ²) : Finset ℝ :=
  A.offDiag.image fun p ↦ dist p.1 p.2

/--
A set of `n` points determines `n-1` distinct distances such that the `i`-th distance
occurs `i` times.
-/
def HasDistanceCounts (A : Finset ℝ²) : Prop :=
  let n := A.card
  ∃ D : Finset ℝ, D.card = n - 1 ∧ Distances A = D ∧
    ∃ f : D ≃ Fin (n - 1),
      ∀ i : Fin (n - 1),
        (A.offDiag.filter fun p ↦ dist p.1 p.2 = f.symm i).card = 2 * (i.val + 1)

/--
For which $n$ are there $n$ points in $\mathbb{R}^2$, no three on a line and no four on a circle,
which determine $n-1$ distinct distances and so that (in some ordering of the distances)
the $i$th distance occurs $i$ times?
-/
@[category research open, AMS 52]
def erdos_217 : Set ℕ :=
  { n | ∃ A : Finset ℝ², A.card = n ∧ NonTrilinear A.toSet ∧
    NoFourConcyclic A.toSet ∧ HasDistanceCounts A }

/--
Palásti has proved such sets exist for all $n \leq 8$.
-/
@[category research solved, AMS 52]
theorem erdos_217.lb : { n | n ≤ 8 } ⊆ erdos_217 := by
  sorry

/--
Erdős believed this is impossible for all sufficiently large $n$.
-/
@[category research open, AMS 52]
theorem erdos_217.sufficiently_large : ∃ N, ∀ n ≥ N, n ∉ erdos_217 := by
  sorry

end Erdos217
