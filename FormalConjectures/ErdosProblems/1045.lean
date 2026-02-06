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
# Erdős Problem 1045

Maximum product of pairwise distances.

OPEN

*Reference:* [erdosproblems.com/1045](https://www.erdosproblems.com/1045)
-/

open Finset

open scoped Topology Real

namespace Erdos1045

/-- Product of pairwise distances -/
noncomputable def Δ (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i ≠ j then Complex.abs (z i - z j) else 1

/-- Maximum product of pairwise distances -/
@[category research open, AMS 52]
theorem max_product_distances (n : ℕ) :
    ∃ (M : ℝ), ∀ (z : Fin n → ℂ),
      (∀ i j : Fin n, Complex.abs (z i - z j) ≤ 2) →
      Δ z ≤ M := by
  sorry

end Erdos1045
