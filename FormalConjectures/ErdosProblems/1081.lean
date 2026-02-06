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
# Erdős Problem 1081

Sums of squarefull numbers.

DISPROVED

*Reference:* [erdosproblems.com/1081](https://www.erdosproblems.com/1081)
-/

open Finset

open scoped Topology Real

namespace Erdos1081

/-- Squarefull number predicate -/
def isSquarefull (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

/-- Sums of squarefull numbers -/
@[category research open, AMS 11]
theorem squarefull_sums (answer : Prop) :
    answer ↔ ∀ n : ℕ, ∃ a b : ℕ,
      isSquarefull a ∧ isSquarefull b ∧ a + b = n := by
  sorry

end Erdos1081
