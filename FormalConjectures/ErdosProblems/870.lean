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
# Erdős Problem 870

Order k basis with large r(n) contains minimal basis.

OPEN

*Reference:* [erdosproblems.com/870](https://www.erdosproblems.com/870)
-/

open Finset

open scoped Topology Real

namespace Erdos870

/-- Additive basis of order k -/
def IsAdditiveBasisK (A : Set ℕ) (k : ℕ) : Prop := sorry

/-- Minimal additive basis of order k -/
def IsMinimalAdditiveBasisK (A : Set ℕ) (k : ℕ) : Prop := sorry

/-- Representation function -/
noncomputable def r (A : Set ℕ) (n : ℕ) : ℕ := sorry

/-- Large r(n) implies contains minimal basis -/
@[category research open, AMS 11]
theorem large_representation_minimal (k : ℕ) (hk : k ≥ 3) (answer : Prop) :
    answer ↔ ∃ c : ℝ, c > 0 ∧
      ∀ (A : Set ℕ),
        IsAdditiveBasisK A k →
        (∀ᶠ (n : ℕ) in Filter.atTop, r A n ≥ c * Real.log n) →
        ∃ (B : Set ℕ), B ⊆ A ∧ IsMinimalAdditiveBasisK B k := by
  sorry

end Erdos870
