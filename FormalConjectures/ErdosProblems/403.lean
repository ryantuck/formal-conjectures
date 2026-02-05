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
# Erdős Problem 403

Does $2^m = a_1! + \cdots + a_k!$ with $a_1 < \cdots < a_k$ have only finitely many solutions?

PROVED by Frankl and Lin: YES. Largest solution is $2^7 = 2! + 3! + 5!$.

Lin also found exactly 5 solutions to $3^m = a_1! + \cdots + a_k!$ (m = 0,1,2,3,6).

*Reference:* [erdosproblems.com/403](https://www.erdosproblems.com/403)
-/

open Filter Topology BigOperators

namespace Erdos403

/-- Frankl-Lin: Only finitely many powers of 2 are sums of distinct factorials -/
@[category research solved, AMS 11]
theorem erdos_403_frankl_lin :
    ∃ B : ℕ, ∀ m : ℕ, ∀ S : Finset ℕ,
      S.sum Nat.factorial = 2^m → m ≤ B := by
  sorry

/-- The largest solution is 2^7 = 2! + 3! + 5! -/
@[category research solved, AMS 11]
theorem erdos_403_largest :
    ∃ S : Finset ℕ, S.sum Nat.factorial = 2^7 ∧
      ∀ m > 7, ∀ T : Finset ℕ, T.sum Nat.factorial ≠ 2^m := by
  sorry

/-- Lin: Exactly 5 solutions for powers of 3 -/
@[category research solved, AMS 11]
theorem erdos_403_powers_of_3 :
    Nat.card {m : ℕ | ∃ S : Finset ℕ, S.sum Nat.factorial = 3^m} = 5 := by
  sorry

end Erdos403
