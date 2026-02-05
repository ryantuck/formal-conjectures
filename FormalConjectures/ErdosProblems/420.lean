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
# Erdős Problem 420

Let $F(f,n) = \tau((n + \lfloor f(n) \rfloor)!) / \tau(n!)$.

Question 1: Is $\lim F((\log n)^C, n) = \infty$ for large C?
Question 2: Is $F(\log n, n)$ dense in $(1,\infty)$?
Question 3: For monotonic $f(n) \leq \log n$ with $f(n) \to \infty$, is $F(f,n)$ dense?

Erdős-Graham-Ivić-Pomerance: $\liminf F(c \log n, n) = 1$ for any c > 0.
van Doorn: Conditional results on bounded prime gaps.

*Reference:* [erdosproblems.com/420](https://www.erdosproblems.com/420)
-/

open Filter Topology BigOperators Real

namespace Erdos420

/-- F(f,n) is the ratio of divisor counts -/
noncomputable def F (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((⌊n + f n⌋₊).factorial.divisors.card : ℝ) / (n.factorial.divisors.card : ℝ)

/-- Erdős-Graham-Ivić-Pomerance: liminf equals 1 -/
@[category research open, AMS 11]
theorem erdos_420_egiop :
    ∀ c > 0, Filter.liminf (fun n => F (fun n => c * log n) n) atTop = 1 := by
  sorry

/-- Erdős-Graham: Growth with square root -/
@[category research open, AMS 11]
theorem erdos_420_sqrt_growth :
    ∃ c : ℝ, 0 < c ∧ c < 1/2 ∧
      Tendsto (F (fun n => (n : ℝ) ^ c)) atTop atTop := by
  sorry

end Erdos420
