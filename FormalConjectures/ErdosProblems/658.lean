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
# Erdős Problem 658

If A ⊆ {1,...,N}² with |A| ≥ δN² for δ>0 and large N, must A contain vertices of a square?

PROVED by Solymosi (2004); qualitative proof from density Hales-Jewett

*Reference:* [erdosproblems.com/658](https://www.erdosproblems.com/658)
-/

open Finset

open scoped Topology Real

namespace Erdos658

/-- Dense subset of grid contains axis-aligned square -/
@[category research solved, AMS 05]
theorem dense_grid_contains_square (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ (N : ℕ) in Filter.atTop,
      ∀ (A : Finset (ℕ × ℕ)),
        (∀ p ∈ A, p.1 ≤ N ∧ p.2 ≤ N) →
        A.card ≥ Nat.floor (δ * N^2) →
        ∃ a d : ℕ, d > 0 ∧
          (a, a) ∈ A ∧ (a+d, a) ∈ A ∧ (a, a+d) ∈ A ∧ (a+d, a+d) ∈ A := by
  sorry

end Erdos658
