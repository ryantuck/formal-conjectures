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
# Erdős Problem 844

Maximum set with non-squarefree products.

SOLVED

*Reference:* [erdosproblems.com/844](https://www.erdosproblems.com/844)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos844

/-- Squarefree -/
def Squarefree (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ^ 2 ∣ n → False

/-- Maximum set with non-squarefree products -/
@[category research solved, AMS 11]
theorem non_squarefree_products (N : ℕ) :
    ∃ (A : Finset ℕ),
      A ⊆ Finset.range (N + 1) ∧
      (∀ a b : ℕ, a ∈ A → b ∈ A → ¬Squarefree (a * b)) ∧
      A.card = sorry := by
  sorry

end Erdos844
