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
# Erdős Problem 1110

Representability using powers of coprime integers.

OPEN

*Reference:* [erdosproblems.com/1110](https://www.erdosproblems.com/1110)
-/

open Finset

open scoped Topology Real

namespace Erdos1110

/-- Representability using powers of coprime integers -/
@[category research open, AMS 11]
theorem coprime_power_representation (answer : Prop) :
    answer ↔ ∀ n : ℕ, ∃ a b k : ℕ,
      Nat.Coprime a b ∧ n = a^k + b^k := by
  sorry

end Erdos1110
