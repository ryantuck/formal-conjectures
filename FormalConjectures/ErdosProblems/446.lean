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
# Erdős Problem 446

Let δ(n) denote the density of integers divisible by some integer in (n,2n).

Questions:
1. What is the growth rate of δ(n)?
2. If δ₁(n) is the density of integers with exactly one divisor in (n,2n), is δ₁(n)=o(δ(n))?

Ford: SOLVED - Determined δ(n) ≍ 1/((log n)^α(log log n)^(3/2)) where α≈0.08607.
Ford: DISPROVED question 2 - Proved δᵣ(n) ≫ᵣ δ(n) for all r.

*Reference:* [erdosproblems.com/446](https://www.erdosproblems.com/446)
-/

open Filter Topology BigOperators Real

namespace Erdos446

/-- δ(n) is the density of integers with divisors in (n,2n) -/
noncomputable def delta (n : ℕ) : ℝ :=
  (Nat.card {m : ℕ | m > 0 ∧ ∃ d : ℕ, n < d ∧ d ≤ 2 * n ∧ d ∣ m} : ℝ) /
  (Nat.card {m : ℕ | m > 0} : ℝ)

/-- δᵣ(n) is the density with exactly r divisors in (n,2n) -/
noncomputable def delta_r (r n : ℕ) : ℝ :=
  (Nat.card {m : ℕ | m > 0 ∧ Nat.card {d : ℕ | n < d ∧ d ≤ 2 * n ∧ d ∣ m} = r} : ℝ) /
  (Nat.card {m : ℕ | m > 0} : ℝ)

/-- Ford: Asymptotic formula for δ(n) -/
@[category research solved, AMS 11]
theorem erdos_446_ford_growth :
    ∃ α : ℝ, α > 0 ∧ ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ / ((log n) ^ α * (log (log n)) ^ ((3:ℝ)/2)) ≤ delta n ∧
      delta n ≤ c₂ / ((log n) ^ α * (log (log n)) ^ ((3:ℝ)/2)) := by
  sorry

/-- Ford: δᵣ(n) is not o(δ(n)) -/
@[category research solved, AMS 11]
theorem erdos_446_ford_disproved :
    ∀ r : ℕ, ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      delta_r r n ≥ c * delta n := by
  sorry

end Erdos446
