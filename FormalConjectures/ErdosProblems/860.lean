/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 860

h(n) for prime divisibility in intervals.

OPEN

*Reference:* [erdosproblems.com/860](https://www.erdosproblems.com/860)
-/

open Finset Nat Filter Asymptotics

open scoped Topology Real

namespace Erdos860

/-- h(n): minimal interval length such that any interval (m, m+h(n)) contains
    distinct integers aᵢ with pᵢ | aᵢ for all primes p₁,...,p_π(n) -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {h : ℕ | ∀ m : ℕ, m ≥ 1 →
    ∃ a : Fin (Nat.card {p : ℕ | p.Prime ∧ p ≤ n}) → ℕ,
      (∀ i j, i ≠ j → a i ≠ a j) ∧
      (∀ i, m < a i ∧ a i < m + h) ∧
      (∀ i, ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ p ∣ a i)}

/-- Main question: estimate h(n) -/
@[category research open, AMS 11]
theorem estimate_h :
    ∃ f : ℕ → ℝ, (fun n => (h n : ℝ)) ~[atTop] f := by
  sorry

/-- Erdős-Pomerance upper bound: h(n) ≪ n^(3/2) / √(log n) -/
@[category research solved, AMS 11]
theorem erdos_pomerance_upper :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≤ C * (n : ℝ) ^ (3/2) / Real.sqrt (Real.log n) := by
  sorry

/-- Erdős-Selfridge lower bound: h(n) > (3 - o(1))n -/
@[category research solved, AMS 11]
theorem erdos_selfridge_lower :
    ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀,
      (h n : ℝ) > (3 - ε) * n := by
  sorry

/-- Ruzsa: h(n)/n → ∞ -/
@[category research solved, AMS 11]
theorem ruzsa_divergence :
    Filter.Tendsto (fun n => (h n : ℝ) / n) atTop atTop := by
  sorry

end Erdos860
