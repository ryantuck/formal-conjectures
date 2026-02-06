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
# Erdős Problem 858

Set avoiding specific divisibility.

OPEN

*Reference:* [erdosproblems.com/858](https://www.erdosproblems.com/858)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos858

/-- Maximum reciprocal sum avoiding divisibility -/
@[category research open, AMS 11]
theorem divisibility_reciprocal_sum (N : ℕ) :
    ∃ (A : Finset ℕ),
      A ⊆ Finset.range (N + 1) ∧
      (∀ a b t : ℕ, a ∈ A → b ∈ A →
        a * t = b →
        ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ p ≤ a) →
      sorry := by
  sorry

end Erdos858
