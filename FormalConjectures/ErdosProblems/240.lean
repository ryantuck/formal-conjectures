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
# Erdős Problem 240

*Reference:* [erdosproblems.com/240](https://www.erdosproblems.com/240)
-/

open Filter Topology

namespace Erdos240

/--
The sequence of integers divisible only by primes in $P$, in increasing order.
-/
def SmoothIntegers (P : Set ℕ) : ℕ → ℕ := sorry

/--
Is there an infinite set of primes $P$ such that if $\{a_1<a_2<\cdots\}$ is the set
of integers divisible only by primes in $P$ then $\lim a_{i+1}-a_i=\infty$?

Originally asked to Erdős by Wintner. Tijdeman [Ti73] resolved this question,
proving that for any $\epsilon>0$, there exists an infinite set of primes $P$ such that
$a_{i+1}-a_i \gg a_i^{1-\epsilon}$.

[Ti73] Tijdeman, R., _On integers with many small prime factors_.
  Compositio Math. (1973), 307-316.
-/
@[category research solved, AMS 11]
theorem erdos_240 : ∃ P : Set ℕ,
    Set.Infinite P ∧
    (∀ p ∈ P, Nat.Prime p) ∧
    let a := SmoothIntegers P
    Tendsto (fun i => a (i + 1) - a i) atTop atTop := by
  sorry

/--
Tijdeman proved that for any $\epsilon>0$, there exists an infinite set of primes $P$
such that $a_{i+1}-a_i \gg a_i^{1-\epsilon}$.
-/
@[category research solved, AMS 11]
theorem erdos_240.tijdeman : ∀ ε : ℝ, ε > 0 →
    ∃ P : Set ℕ, ∃ C : ℝ, C > 0 ∧
    Set.Infinite P ∧
    (∀ p ∈ P, Nat.Prime p) ∧
    let a := SmoothIntegers P
    ∀ i : ℕ, i > 0 → (a (i + 1) - a i : ℝ) ≥ C * (a i : ℝ) ^ (1 - ε) := by
  sorry

end Erdos240
