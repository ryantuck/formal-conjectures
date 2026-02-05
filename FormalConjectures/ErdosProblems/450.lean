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
# Erdős Problem 450

How large must y = y(ε,n) be such that the number of integers in (x, x+y) with
a divisor in (n, 2n) is at most ε·y?

Partial results:
- If must hold for all x: No such y exists when ε(log n)^δ(log log n)^(3/2) → ∞
- When ε ≪ 1/n: y(ε,n) ~ 2n

*Reference:* [erdosproblems.com/450](https://www.erdosproblems.com/450)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos450

/-- Count of integers in interval with divisor in (n, 2n) -/
noncomputable def countWithDivisor (x y n : ℕ) : ℕ :=
  Nat.card {m : ℕ | x < m ∧ m ≤ x + y ∧ ∃ d : ℕ, n < d ∧ d ≤ 2*n ∧ d ∣ m}

/-- No uniform bound when ε grows with n -/
@[category research open, AMS 11]
theorem erdos_450_no_uniform :
    ∀ δ : ℝ, δ > 0 → ∀ ε : ℝ → ℝ,
      Tendsto (fun n : ℕ => ε n * (log n)^δ * (log (log n))^((3:ℝ)/2)) atTop atTop →
      ∀ᶠ n : ℕ in atTop, ∀ y : ℕ, ∃ x : ℕ, (countWithDivisor x y n : ℝ) > ε n * y := by
  sorry

/-- When ε is small, y ~ 2n suffices -/
@[category research open, AMS 11]
theorem erdos_450_small_epsilon :
    ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, ε * n ≥ 1 →
      ∃ y : ℕ, y ≤ 3*n ∧ ∀ x : ℕ, (countWithDivisor x y n : ℝ) ≤ ε * y := by
  sorry

end Erdos450
