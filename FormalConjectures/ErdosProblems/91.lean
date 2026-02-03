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

/-!
# Erdős Problem 91

*Reference:* [erdosproblems.com/91](https://www.erdosproblems.com/91)
-/

namespace Erdos91

open scoped EuclideanGeometry

/--
Let $n$ be a sufficently large integer. Suppose $A\subset \mathbb{R}^2$ has $|A|=n$ and minimises
the number of distinct distances between points in $A$. Prove that there are at least two (and
probably many) such $A$ which are non-similar.
-/
noncomputable def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (Finset.image (fun p : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) ↦ dist p.1 p.2)
    (A.product A)).card

@[category research open, AMS 52]
theorem erdos_91 : answer(sorry) ↔ ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    let min_dist := sInf { k | ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n ∧ distinctDistances A = k }
    let optimizers := { A : Finset (EuclideanSpace ℝ (Fin 2)) | A.card = n ∧ distinctDistances A = min_dist }
    ∃ (A B : Finset (EuclideanSpace ℝ (Fin 2))), A ∈ optimizers ∧ B ∈ optimizers ∧
    ¬ (∃ (c : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      c > 0 ∧ (∀ x y, dist (f x) (f y) = c * dist x y) ∧
      B = A.image f) := by
  sorry

end Erdos91