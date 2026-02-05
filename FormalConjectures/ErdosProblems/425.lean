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
# Erdős Problem 425

Let F(n) be the maximum size of $A \subseteq \{1,\ldots,n\}$ where all products ab (a < b) are distinct.

Is $F(n) = \pi(n) + (c + o(1)) n^{3/4} (\log n)^{-3/2}$ for some constant c?

Erdős established bounds with constants $c_1, c_2$.

*Reference:* [erdosproblems.com/425](https://www.erdosproblems.com/425)
-/

open Filter Topology BigOperators Real

namespace Erdos425

/-- F(n) is the maximum size of set with distinct pairwise products -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 0 < a ∧ a ≤ n) ∧
    ∀ a ∈ A, ∀ b ∈ A, a < b → ∀ c ∈ A, ∀ d ∈ A, c < d → (a, b) ≠ (c, d) → a * b ≠ c * d}

/-- Prime counting function π(n) -/
noncomputable def primeCount (n : ℕ) : ℕ := Nat.card {p : ℕ | p ≤ n ∧ p.Prime}

/-- Erdős: Asymptotic bounds -/
@[category research open, AMS 11]
theorem erdos_425_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      (primeCount n : ℝ) + c₁ * (n : ℝ)^((3:ℝ)/4) / (log n)^((3:ℝ)/2) ≤ (F n : ℝ) ∧
      (F n : ℝ) ≤ (primeCount n : ℝ) + c₂ * (n : ℝ)^((3:ℝ)/4) / (log n)^((3:ℝ)/2) := by
  sorry

end Erdos425
