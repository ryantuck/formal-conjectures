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
# Erdős Problem 423

Define $a_1 = 1$, $a_2 = 2$, and for $k \geq 3$, $a_k$ is the least integer greater than
$a_{k-1}$ that equals the sum of at least two consecutive terms.

What is the asymptotic behavior of this sequence? (Hofstadter-Ulam sequence)

Bolan & Tang: Infinitely many integers don't appear, and $a_n - n$ is nondecreasing and unbounded.

*Reference:* [erdosproblems.com/423](https://www.erdosproblems.com/423)
-/

open Filter Topology BigOperators

namespace Erdos423

/-- The Hofstadter-Ulam sequence -/
def hofstadter_ulam : ℕ → ℕ := sorry

/-- Bolan-Tang: Infinitely many integers missing from sequence -/
@[category research open, AMS 11]
theorem erdos_423_bolan_tang_missing :
    ∀ M : ℕ, ∃ n > M, n ∉ Set.range hofstadter_ulam := by
  sorry

/-- Bolan-Tang: The difference a_n - n is nondecreasing and unbounded -/
@[category research open, AMS 11]
theorem erdos_423_bolan_tang_difference :
    (∀ n : ℕ, hofstadter_ulam n - n ≤ hofstadter_ulam (n + 1) - (n + 1)) ∧
    (∀ M : ℕ, ∃ n : ℕ, hofstadter_ulam n - n > M) := by
  sorry

end Erdos423
