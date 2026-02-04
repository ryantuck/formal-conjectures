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
# Erdős Problem 282

*Reference:* [erdosproblems.com/282](https://www.erdosproblems.com/282)
-/

open Filter Topology

namespace Erdos282

/--
Given an infinite set $A \subseteq \mathbb{N}$ and a rational $x \in (0,1)$, apply the greedy
algorithm: repeatedly select the minimal $n \in A$ where $n \geq 1/x$, then replace $x$ with
$x - 1/n$ until termination.

Primary question: Does termination always occur when $x$ has odd denominator and $A$ is the
set of odd numbers?

Fibonacci (1202) proved termination for all $x$ when $A = \mathbb{N}$.
-/
@[category research open, AMS 11]
theorem erdos_282_odd_denominator :
    ∀ x : ℚ, 0 < x → x < 1 → (∃ q : ℕ, Odd q ∧ x.den = q) →
      ∃ (k : ℕ) (a : Fin k → ℕ),
        (∀ i, Odd (a i)) ∧
        (∀ i j, i ≠ j → a i ≠ a j) ∧
        (x : ℝ) = ∑ i : Fin k, (1 : ℝ) / (a i : ℝ) := by
  sorry

/--
Fibonacci (1202): The greedy algorithm terminates for all $x$ when $A = \mathbb{N}$.
-/
@[category research solved, AMS 11]
theorem erdos_282_fibonacci (x : ℚ) (h0 : 0 < x) (h1 : x < 1) :
    ∃ (k : ℕ) (a : Fin k → ℕ),
      (∀ i, a i ≥ 1) ∧
      (∀ i j, i ≠ j → a i ≠ a j) ∧
      (x : ℝ) = ∑ i : Fin k, (1 : ℝ) / (a i : ℝ) := by
  sorry

end Erdos282
