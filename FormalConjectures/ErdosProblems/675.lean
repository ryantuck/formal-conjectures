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
# Erdős Problem 675

The translation property of subsets: Does the set of sums of two squares have it?
For squarefree numbers, how quickly does minimal t_n grow?

OPEN

*Reference:* [erdosproblems.com/675](https://www.erdosproblems.com/675)
-/

open Nat

open scoped Topology Real

namespace Erdos675

/-- Translation property: ∀n ∃t_n ≥ 1 such that a ∈ A ↔ a+t_n ∈ A for all 1≤a≤n -/
def HasTranslationProperty (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ t_n : ℕ, t_n ≥ 1 ∧
    ∀ a : ℕ, 1 ≤ a ∧ a ≤ n → (a ∈ A ↔ a + t_n ∈ A)

/-- Does the set of sums of two squares have the translation property? -/
@[category research open, AMS 11]
theorem sum_of_two_squares_translation_property (answer : Prop) :
    answer ↔ HasTranslationProperty {n : ℕ | ∃ a b : ℤ, n = a^2 + b^2} := by
  sorry

end Erdos675
