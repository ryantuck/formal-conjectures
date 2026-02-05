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
# Erdős Problem 407

Define $w(n)$ as the count of solutions to $n = 2^a + 3^b + 2^c 3^d$ with $a,b,c,d \geq 0$.
Is w(n) bounded by an absolute constant?

PROVED: YES. Evertse-Györy-Stewart-Tijdeman (1988): w(n) is bounded.
Tijdeman-Wang (1988): w(n) ≤ 4 for large n.
Bajpai-Bennett (2024): w(n) ≤ 4 for n ≥ 131082, w(n) ≤ 9 always, max is w(299) = 9.

*Reference:* [erdosproblems.com/407](https://www.erdosproblems.com/407)
-/

open Filter Topology BigOperators

namespace Erdos407

/-- Count of representations as 2^a + 3^b + 2^c·3^d -/
noncomputable def w (n : ℕ) : ℕ :=
  Nat.card {quad : ℕ × ℕ × ℕ × ℕ | n = 2^quad.1 + 3^quad.2.1 + 2^quad.2.2.1 * 3^quad.2.2.2}

/-- Evertse-Györy-Stewart-Tijdeman: w(n) is bounded -/
@[category research solved, AMS 11]
theorem erdos_407_egst :
    ∃ B : ℕ, ∀ n : ℕ, w n ≤ B := by
  sorry

/-- Bajpai-Bennett: Effective bound -/
@[category research solved, AMS 11]
theorem erdos_407_bajpai_bennett :
    (∀ n ≥ 131082, w n ≤ 4) ∧ (∀ n : ℕ, w n ≤ 9) ∧ w 299 = 9 := by
  sorry

end Erdos407
