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
# Erdős Problem 309

Given $N \geq 1$, how many integers can be expressed as sums of distinct unit fractions
with denominators from $\{1, \ldots, N\}$? Specifically, does this count grow as $o(\log N)$?

Trivial upper bound: $N(n) \leq \log n + O(1)$.
Yokota (1997): $N(n) \geq \log n - O(\log \log n)$.
Croot (1999) and Yokota (2002) established tight bounds, disproving the $o(\log N)$ conjecture.

*Reference:* [erdosproblems.com/309](https://www.erdosproblems.com/309)
-/

open Filter Topology BigOperators Real

namespace Erdos309

/-- The set of integers representable as sums of distinct unit fractions
    with denominators in {1,...,N} -/
def RepresentableIntegers (N : ℕ) : Set ℕ :=
  {k : ℕ | ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ n ≤ N) ∧ (k : ℚ) = S.sum (fun n => (1 : ℚ) / n)}

/-- The count of representable integers -/
noncomputable def F (N : ℕ) : ℕ :=
  Nat.card (RepresentableIntegers N)

/-- Trivial upper bound: F(N) ≤ log N + O(1) -/
@[category research solved, AMS 11]
theorem erdos_309_upper_bound :
    ∃ C : ℝ, ∀ N : ℕ, N > 0 →
      (F N : ℝ) ≤ log N + C := by
  sorry

/-- Yokota (1997): Lower bound with log log term -/
@[category research solved, AMS 11]
theorem erdos_309_yokota_1997 :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      (F N : ℝ) ≥ log N - C * log (log N) := by
  sorry

/-- Yokota (2002): Improved lower bound with Euler-Mascheroni constant -/
@[category research solved, AMS 11]
theorem erdos_309_yokota_2002 :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      (F N : ℝ) ≥ log N + 0.577 - (Real.pi^2/3) * (log (log N))^2 / log N - C := by
  sorry

/-- The answer is NO: F(N) is not o(log N), it is Θ(log N) -/
@[category research solved, AMS 11]
theorem erdos_309_not_little_o :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop, (F N : ℝ) ≥ c * log N := by
  sorry

end Erdos309
