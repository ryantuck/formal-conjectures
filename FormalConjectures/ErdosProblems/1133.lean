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
# Erdős Problem 1133

Existence of polynomials with large bounds.

OPEN

*Reference:* [erdosproblems.com/1133](https://www.erdosproblems.com/1133)
-/

open Finset

open scoped Topology Real

namespace Erdos1133

/-- Existence of polynomials with large bounds -/
@[category research open, AMS 41]
theorem polynomial_large_bounds (C : ℝ) (hC : 0 < C) :
    ∃ (ε : ℝ), 0 < ε ∧
      ∀ᶠ n in Filter.atTop, ∀ (x : Fin n → ℝ),
        (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) →
        ∃ (y : Fin n → ℝ),
          (∀ i, y i ∈ Set.Icc (-1 : ℝ) 1) ∧
          sorry := by
  sorry

end Erdos1133
