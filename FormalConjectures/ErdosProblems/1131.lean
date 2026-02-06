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
# Erdős Problem 1131

Integral of squared Lagrange basis functions.

OPEN

*Reference:* [erdosproblems.com/1131](https://www.erdosproblems.com/1131)
-/

open Finset

open scoped Topology Real

namespace Erdos1131

/-- Integral of squared Lagrange basis functions -/
noncomputable def I (x : Fin n → ℝ) : ℝ := sorry

/-- Minimum integral of squared Lagrange basis functions -/
@[category research open, AMS 41]
theorem lagrange_basis_integral_minimum (n : ℕ) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (x : Fin n → ℝ), (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) →
        I x ≥ 2 - (1 + c) / n := by
  sorry

end Erdos1131
