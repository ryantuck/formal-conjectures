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
# Erdős Problem 1113

Sierpinski numbers without finite covering sets.

OPEN

*Reference:* [erdosproblems.com/1113](https://www.erdosproblems.com/1113)
-/

open Finset

open scoped Real

namespace Erdos1113

/-- Sierpinski numbers without finite covering sets.
    Asks whether there exists an odd k such that k·2ⁿ+1 is never prime,
    but k doesn't have a finite covering set of primes. -/
@[category research open, AMS 11]
theorem sierpinski_without_covering :
    answer(sorry) ↔ ∃ k : ℕ, Odd k ∧
      (∀ n : ℕ, ¬ Nat.Prime (k * 2^n + 1)) ∧
      (¬ ∃ (S : Finset ℕ), ∀ p ∈ S, Nat.Prime p ∧
        ∀ n : ℕ, ∃ p ∈ S, p ∣ (k * 2^n + 1)) := by
  sorry

end Erdos1113
