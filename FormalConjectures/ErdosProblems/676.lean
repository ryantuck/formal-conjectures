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
# Erdős Problem 676

Is every sufficiently large integer of the form ap² + b for some prime p
and integer a ≥ 1 and 0 ≤ b < p?

OPEN (Erdős believed it "rather unlikely")

*Reference:* [erdosproblems.com/676](https://www.erdosproblems.com/676)
-/

open Nat

open scoped Topology Real

namespace Erdos676

/-- All large integers have form ap² + b -/
@[category research open, AMS 11]
theorem large_integers_prime_square_form (answer : Prop) :
    answer ↔ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ (p a b : ℕ), p.Prime ∧ a ≥ 1 ∧ b < p ∧
        n = a * p^2 + b := by
  sorry

end Erdos676
