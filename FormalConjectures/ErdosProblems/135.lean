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
# Erdős Problem 135

*Reference:* [erdosproblems.com/135](https://www.erdosproblems.com/135)
-/

namespace Erdos135

open Finset Real Metric Classical

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/--
A simpler definition of number of distances.
-/
noncomputable def NumDistances' (A : Finset V) : ℕ :=
  Finset.card (Finset.image (fun p : V × V => dist p.1 p.2) ((A.product A).filter (fun p => p.1 ≠ p.2)))

/--
Any subset of size 4 determines at least 5 distinct distances.
-/
def FourPointsFiveDistances (A : Finset V) : Prop :=
  ∀ S ⊆ A, S.card = 4 → NumDistances' S ≥ 5

/--
The conjecture is that if `A` satisfies `FourPointsFiveDistances`, then it determines $\gg n^2$ distances.
Tao [Ta24c] proved this is false.
-/
@[category research solved, AMS 52]
theorem erdos_135 :
    answer(False) ↔ ∃ C > 0, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      A.card ≥ 4 → FourPointsFiveDistances A → (NumDistances' A : ℝ) ≥ C * (A.card : ℝ) ^ 2 := by
  sorry

end Erdos135
