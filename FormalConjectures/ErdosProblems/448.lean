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
# Erdős Problem 448

Let τ(n) denote the count of divisors of n, and τ⁺(n) denote the number of values k
such that n has a divisor in [2^k, 2^(k+1)). For all ε > 0, is it true that
τ⁺(n) < ε·τ(n) for almost all n?

Erdős-Tenenbaum: DISPROVED - Upper density is ≍ ε^(1-o(1)).

Ford: Proved ∑_{n ≤ x} τ⁺(n) ≍ x·(log x)^(1-α)/(log log x)^(3/2) where α ≈ 0.08607.

*Reference:* [erdosproblems.com/448](https://www.erdosproblems.com/448)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos448

/-- τ⁺(n) counts dyadic ranges with divisors -/
noncomputable def tau_plus (n : ℕ) : ℕ :=
  Nat.card {k : ℕ | ∃ d : ℕ, d ∣ n ∧ 2^k ≤ d ∧ d < 2^(k+1)}

/-- Erdős-Tenenbaum: Density bound -/
@[category research solved, AMS 11]
theorem erdos_448_erdos_tenenbaum :
    ∀ ε > 0, ∃ c : ℝ, c > 0 ∧
      limsup (fun N : ℕ => (Nat.card {n ≤ N | (tau_plus n : ℝ) < ε * n.divisors.card} : ℝ) / N) atTop
        ≤ c * ε := by
  sorry

/-- Ford: Sum formula -/
@[category research solved, AMS 11]
theorem erdos_448_ford :
    ∃ α c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ x : ℕ in atTop,
      c₁ * x * (log x)^(1 - α) / (log (log x))^((3:ℝ)/2) ≤
        (Finset.range x).sum (fun n => (tau_plus n : ℝ)) ∧
      (Finset.range x).sum (fun n => (tau_plus n : ℝ)) ≤
        c₂ * x * (log x)^(1 - α) / (log (log x))^((3:ℝ)/2) := by
  sorry

end Erdos448
