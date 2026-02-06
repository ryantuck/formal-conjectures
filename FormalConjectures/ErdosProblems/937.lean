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
# Erdős Problem 937

Arithmetic progressions of coprime powerful numbers.

PROVED

*Reference:* [erdosproblems.com/937](https://www.erdosproblems.com/937)
-/

open Finset

open scoped Topology Real

namespace Erdos937

/-- A number is powerful if p^2 | n for all primes p | n -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Arithmetic progressions of coprime powerful numbers exist -/
@[category research solved, AMS 11]
theorem coprime_powerful_ap (k : ℕ) :
    ∃ (a d : ℕ), 0 < d ∧
      (∀ i < k, IsPowerful (a + i * d)) ∧
      (∀ i j : ℕ, i < k → j < k → i ≠ j → Nat.Coprime (a + i * d) (a + j * d)) := by
  sorry

end Erdos937
