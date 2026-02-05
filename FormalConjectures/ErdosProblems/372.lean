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
# Erdős Problem 372

Let $P(n)$ denote the largest prime factor of $n$. There exist infinitely many values
of $n$ satisfying $P(n) > P(n+1) > P(n+2)$.

Erdős-Pomerance conjectured this in 1978. Balog (2001) proved it, showing there are
$\gg \sqrt{x}$ such n ≤ x. Balog conjectured these have density 1/6.

*Reference:* [erdosproblems.com/372](https://www.erdosproblems.com/372)
-/

open Filter Topology BigOperators Real

namespace Erdos372

/-- Largest prime factor of n -/
noncomputable def P (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ p ∣ n}

/-- Balog (2001): Infinitely many n with P(n) > P(n+1) > P(n+2) -/
@[category research solved, AMS 11]
theorem erdos_372_balog :
    ∃ᶠ n : ℕ in atTop, P n > P (n + 1) ∧ P (n + 1) > P (n + 2) := by
  sorry

/-- Balog: Lower bound on count -/
@[category research solved, AMS 11]
theorem erdos_372_balog_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ x : ℕ in atTop,
      (Nat.card {n : ℕ | n ≤ x ∧ P n > P (n + 1) ∧ P (n + 1) > P (n + 2)} : ℝ) ≥
        c * Real.sqrt x := by
  sorry

end Erdos372
