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
# Erdős Problem 683

For every 1 ≤ k ≤ n, does P(C(n,k)) ≥ min(n-k+1, k^{1+c}) for some constant c > 0,
where P denotes the largest prime divisor?

OPEN (Erdős proved P(C(n,k)) ≫ k log k for k ≤ n/2)

*Reference:* [erdosproblems.com/683](https://www.erdosproblems.com/683)
-/

open Nat

open scoped Topology Real

namespace Erdos683

/-- P(n): largest prime divisor of n -/
noncomputable def P (n : ℕ) : ℕ := sorry

/-- Largest prime divisor of binomial coefficient bound -/
@[category research open, AMS 11]
theorem binomial_largest_prime_divisor (answer : Prop) :
    answer ↔ ∃ c > 0, ∀ n k : ℕ, 1 ≤ k ∧ k ≤ n →
      P (Nat.choose n k) ≥ min (n - k + 1) (Nat.floor ((k : ℝ) ^ (1 + c))) := by
  sorry

end Erdos683
