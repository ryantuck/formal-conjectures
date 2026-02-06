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
# Erdős Problem 773

Sidon subset of perfect squares.

OPEN

*Reference:* [erdosproblems.com/773](https://www.erdosproblems.com/773)
-/

open Finset

open scoped Topology Real

namespace Erdos773

/-- Sidon property -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Maximum Sidon subset of squares -/
@[category research open, AMS 11]
theorem sidon_squares_bound (N : ℕ) (answer : Prop) :
    answer ↔ ∃ (A : Finset ℕ),
      (∀ a ∈ A, ∃ k ≤ N, a = k ^ 2) ∧
      IsSidon A ∧
      A.card ≥ (N : ℝ) ^ (1 - sorry) := by
  sorry

end Erdos773
