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
# Erdős Problem 759

Maximum cochromatic number on surfaces.

SOLVED

*Reference:* [erdosproblems.com/759](https://www.erdosproblems.com/759)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos759

variable {α : Type*}

/-- Cochromatic number -/
noncomputable def cochromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- z(S_n): maximum cochromatic number on genus n surface -/
noncomputable def z_surface (n : ℕ) : ℕ := sorry

/-- Growth rate z(S_n) ≍ √n/log n -/
@[category research solved, AMS 05]
theorem cochromatic_surface_growth :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        c₁ * (n : ℝ) ^ (1/2 : ℝ) / Real.log n ≤ z_surface n ∧
        z_surface n ≤ c₂ * (n : ℝ) ^ (1/2 : ℝ) / Real.log n := by
  sorry

end Erdos759
