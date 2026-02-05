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
# Erdős Problem 394

Let $t_k(n)$ be the least $m$ such that $n \mid m(m+1)\cdots(m+k-1)$.

Question 1: Is $\sum_{n \leq x} t_2(n) \ll x^2/(\log x)^c$ for some c > 0?
Question 2: For k ≥ 2, is $\sum_{n \leq x} t_{k+1}(n) = o(\sum_{n \leq x} t_k(n))$?

Erdős-Hall: $\sum t_2(n) \ll x^2 \log\log\log x / \log\log x$.
Trivial lower bound: $\sum t_2(n) \gg x^2 / \log x$ (from primes).

*Reference:* [erdosproblems.com/394](https://www.erdosproblems.com/394)
-/

open Filter Topology BigOperators Real

namespace Erdos394

/-- t_k(n) is the least m such that n divides k consecutive integers starting from m -/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf {m : ℕ | n ∣ (Finset.Ico m (m + k)).prod id}

/-- Erdős-Hall: Upper bound for sum of t_2 -/
@[category research open, AMS 11]
theorem erdos_394_erdos_hall :
    ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x > 0 →
      ((Finset.range x).sum (fun n => (t 2 n : ℝ))) ≤
        C * x^2 * log (log (log x)) / log (log x) := by
  sorry

/-- Lower bound from primes -/
@[category research open, AMS 11]
theorem erdos_394_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ x : ℕ in atTop,
      ((Finset.range x).sum (fun n => (t 2 n : ℝ))) ≥ c * x^2 / log x := by
  sorry

end Erdos394
