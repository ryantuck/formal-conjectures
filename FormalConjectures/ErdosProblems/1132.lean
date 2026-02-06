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
# Erdős Problem 1132

Absolute value sums in Lagrange interpolation.

OPEN

*Reference:* [erdosproblems.com/1132](https://www.erdosproblems.com/1132)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1132

/-- Sum of absolute values of Lagrange basis functions -/
noncomputable def L (x : Fin n → ℝ) (t : ℝ) : ℝ := sorry

/-- Absolute value sums in Lagrange interpolation exceed logarithmic bound -/
@[category research open, AMS 41]
theorem lagrange_absolute_value_sums (answer : Prop) :
    answer ↔ ∀ (seq : ℕ → (Fin n → ℝ)),
      (∀ n i, seq n i ∈ Set.Icc (-1 : ℝ) 1) →
      ∃ (t : ℝ), t ∈ Set.Ioo (-1 : ℝ) 1 ∧
        (∀ᶠ n in atTop, L (seq n) t > (2 / Real.pi) * Real.log n - sorry) := by
  sorry

end Erdos1132
