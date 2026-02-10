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
# Erdős Problem 896

Maximum F(A,B) for unique factorization.

OPEN

*Reference:* [erdosproblems.com/896](https://www.erdosproblems.com/896)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos896

/-- F(A,B): count of m with unique factorization m = ab where a ∈ A, b ∈ B -/
noncomputable def F (A B : Finset ℕ) : ℕ :=
  {m : ℕ | ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ m = p.1 * p.2}.ncard

/-- Van Doorn lower bound: max F(A,B) ≥ (1+o(1))N²/log N -/
@[category research solved, AMS 11]
theorem van_doorn_lower :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A B : Finset ℕ, (∀ a ∈ A, a ≤ N) ∧ (∀ b ∈ B, b ≤ N) ∧
        (F A B : ℝ) ≥ (1 - ε) * (N : ℝ) ^ 2 / Real.log N := by
  sorry

/-- Van Doorn upper bound: max F(A,B) ≪ N²/(log N)^δ(log log N)^(3/2) where δ ≈ 0.086 -/
@[category research solved, AMS 11]
theorem van_doorn_upper :
    ∃ C δ : ℝ, C > 0 ∧ δ > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      ∀ A B : Finset ℕ, (∀ a ∈ A, a ≤ N) → (∀ b ∈ B, b ≤ N) →
        (F A B : ℝ) ≤ C * (N : ℝ) ^ 2 / ((Real.log N) ^ δ * (Real.log (Real.log N)) ^ (3/2)) := by
  sorry

/-- Main question: estimate max F(A,B) -/
@[category research open, AMS 11]
theorem unique_factorization_maximum :
    ∃ g : ℕ → ℝ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ A B : Finset ℕ, (∀ a ∈ A, a ≤ N) → (∀ b ∈ B, b ≤ N) →
        (1 - ε) * g N ≤ (F A B : ℝ) ∧ (F A B : ℝ) ≤ (1 + ε) * g N := by
  sorry

end Erdos896
