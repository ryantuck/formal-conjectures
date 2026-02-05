/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 365

Must either n or n+1 be a square when both are powerful numbers?
Is the count of such pairs with n ≤ x bounded by $(\\log x)^{O(1)}$?

DISPROVED: Golomb found counterexample 12167 = 23³, 12168 = 2³·3²·13².
Walker proved infinitely many counterexamples exist.

*Reference:* [erdosproblems.com/365](https://www.erdosproblems.com/365)
-/

open Filter Topology BigOperators

namespace Erdos365

/-- A number is powerful if all prime exponents are at least 2 -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

/-- Golomb's counterexample -/
@[category research solved, AMS 11]
theorem erdos_365_golomb_counterexample :
    IsPowerful 12167 ∧ IsPowerful 12168 ∧
    ¬∃ k : ℕ, 12167 = k^2 ∧ ¬∃ k : ℕ, 12168 = k^2 := by
  sorry

/-- Walker: Infinitely many consecutive powerful pairs, neither a square -/
@[category research solved, AMS 11]
theorem erdos_365_walker :
    ∃ᶠ n : ℕ in atTop, IsPowerful n ∧ IsPowerful (n + 1) ∧
      (¬∃ k : ℕ, n = k^2) ∧ (¬∃ k : ℕ, n + 1 = k^2) := by
  sorry

end Erdos365
