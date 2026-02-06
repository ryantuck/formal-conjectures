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
# Erdős Problem 1130

Lebesgue constants for Lagrange interpolation.

PROVED

*Reference:* [erdosproblems.com/1130](https://www.erdosproblems.com/1130)
-/

open Finset

open scoped Topology Real

namespace Erdos1130

/-- Lebesgue constant for Lagrange interpolation -/
noncomputable def Λ (x : Fin n → ℝ) : ℝ := sorry

/-- Lebesgue constant bounds -/
@[category research solved, AMS 41]
theorem lebesgue_constant_bounds (n : ℕ) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (x : Fin n → ℝ), (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) →
        Λ x ≥ (2 / Real.pi) * Real.log n - c := by
  sorry

end Erdos1130
