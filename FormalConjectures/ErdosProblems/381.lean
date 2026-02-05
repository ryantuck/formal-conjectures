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
# Erdős Problem 381

A number $n$ is highly composite if $\tau(m) < \tau(n)$ for all $m < n$.
Let $Q(x)$ count highly composite numbers in $[1,x]$.

Is it true that $Q(x) \gg_k (\log x)^k$ for every $k \geq 1$?

DISPROVED: Erdős showed $Q(x) \gg (\log x)^{1+c}$, but Nicolas proved
$Q(x) \ll (\log x)^{O(1)}$, so it grows only polynomially in log x.

*Reference:* [erdosproblems.com/381](https://www.erdosproblems.com/381)
-/

open Filter Topology BigOperators Real

namespace Erdos381

/-- A number is highly composite if it has more divisors than all smaller numbers -/
def IsHighlyComposite (n : ℕ) : Prop :=
  n > 0 ∧ ∀ m < n, m > 0 → (Nat.divisors m).card < (Nat.divisors n).card

/-- Count of highly composite numbers up to x -/
noncomputable def Q (x : ℕ) : ℕ :=
  Nat.card {n : ℕ | n ≤ x ∧ IsHighlyComposite n}

/-- Erdős: Q(x) has lower bound with exponent > 1 -/
@[category research solved, AMS 11]
theorem erdos_381_erdos_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ x : ℕ in atTop,
      (Q x : ℝ) ≥ (log x) ^ (1 + c) := by
  sorry

/-- Nicolas: Q(x) has polynomial upper bound in log x -/
@[category research solved, AMS 11]
theorem erdos_381_nicolas_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ x : ℕ in atTop,
      (Q x : ℝ) ≤ (log x) ^ C := by
  sorry

end Erdos381
