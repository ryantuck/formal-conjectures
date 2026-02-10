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

/-!
# Erdős Problem 991

Discrepancy on spheres.

PROVED

*Reference:* [erdosproblems.com/991](https://www.erdosproblems.com/991)
-/

open Finset MeasureTheory

open scoped Topology Real

namespace Erdos991

/-- Maximum product implies low discrepancy -/
@[category research solved, AMS 11]
theorem sphere_max_product_discrepancy (d : ℕ) :
    ∀ (A : Finset (EuclideanSpace ℝ (Fin d))),
      (∀ p ∈ A, ‖p‖ = 1) →
      (∀ B : Finset (EuclideanSpace ℝ (Fin d)),
        (∀ p ∈ B, ‖p‖ = 1) → B.card = A.card →
        (A.product A |>.filter (fun (p, q) => p ≠ q) |>.prod (fun (p, q) => ‖p - q‖)) ≤
        (B.product B |>.filter (fun (p, q) => p ≠ q) |>.prod (fun (p, q) => ‖p - q‖))) →
      ∀ (C : Set (EuclideanSpace ℝ (Fin d))),
        MeasurableSet C →
        (((A.filter (fun p => p ∈ C)).card : ℝ) - volume C * A.card : ℝ).natAbs =o[atTop] fun _ => (A.card : ℝ) := by
  sorry

end Erdos991
