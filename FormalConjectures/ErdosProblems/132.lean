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

/-!
# Erdős Problem 132

*Reference:* [erdosproblems.com/132](https://www.erdosproblems.com/132)
-/

namespace Erdos132

open Finset Real Metric Classical

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/--
The number of pairs in `A` that are at distance `d`.
-/
noncomputable def DistanceCount (A : Finset V) (d : ℝ) : ℕ :=
  (A.powerset.filter (fun s => s.card = 2 ∧ ∃ u ∈ s, ∃ v ∈ s, u ≠ v ∧ dist u v = d)).card

/--
The property that distance `d` occurs at least once but at most `n` times (where `n = |A|`).
-/
def IsRareDistance (A : Finset V) (d : ℝ) : Prop :=
  let count := DistanceCount A d
  1 ≤ count ∧ count ≤ A.card

/--
The conjecture is that for sufficiently large `n`, there are at least two distinct distances
satisfying `IsRareDistance`.
Hopf and Pannowitz [HoPa34] proved the maximal distance always satisfies the upper bound `n`.
-/
@[category research open, AMS 52]
theorem erdos_132 :
    ∃ N, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card ≥ N →
      ∃ d₁ d₂, d₁ ≠ d₂ ∧ IsRareDistance A d₁ ∧ IsRareDistance A d₂ := by
  sorry

end Erdos132
