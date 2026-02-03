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
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős Problem 130

*Reference:* [erdosproblems.com/130](https://www.erdosproblems.com/130)
-/

namespace Erdos130

open SimpleGraph EuclideanGeometry Set Metric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable (A : Set V)

/--
No three points in `A` are collinear.
-/
def NoThreeCollinear (A : Set V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ {x, y, z}

/--
No four points in `A` are concyclic.
-/
def NoFourConcyclic (A : Set V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ w ∈ A,
    x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w →
    ¬ Concyclic {x, y, z, w}

/--
The graph with vertices `A` where two vertices are joined if their distance is an integer.
-/
def DistanceGraph (A : Set V) : SimpleGraph A :=
  SimpleGraph.fromRel (fun x y => dist x.val y.val ∈ {r : ℝ | ∃ k : ℤ, r = k ∧ k > 0})

/--
The problem asks if the chromatic number of such a graph can be infinite.
We specifically consider `A ⊆ ℝ^2` (Euclidean plane).
-/
@[category research open, AMS 05]
theorem erdos_130 :
    answer(sorry) ↔ ∃ A : Set (EuclideanSpace ℝ (Fin 2)),
      A.Infinite ∧ NoThreeCollinear A ∧ NoFourConcyclic A ∧
      (DistanceGraph A).chromaticNumber ≥ Cardinal.aleph0 := by
  sorry

end Erdos130
