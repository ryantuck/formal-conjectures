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
# Erdős Problem 327

Let $A \subseteq \{1,\ldots,N\}$ satisfy: if $a,b \in A$ with $a \neq b$, then $a+b \nmid ab$.

Question 1: Can $A$ be substantially larger than the set of odd numbers?
Question 2: If the condition becomes $a+b \nmid 2ab$, must $|A| = o(N)$?

van Doorn: Any subset $A$ with $|A| \geq (25/28+o(1))N$ contains distinct $a,b$ where $a+b \mid ab$.

*Reference:* [erdosproblems.com/327](https://www.erdosproblems.com/327)
-/

open Filter Topology BigOperators

namespace Erdos327

/-- A set avoiding unit fraction sums: a+b does not divide ab for distinct elements -/
def AvoidUnitFractionSums (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬((a + b) ∣ (a * b))

/-- van Doorn (2024): Dense subsets must contain pair with a+b | ab -/
@[category research open, AMS 11]
theorem erdos_327_van_doorn :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a ∧ a ≤ N) →
      (A.card : ℝ) ≥ (25/28) * N →
      ¬AvoidUnitFractionSums A := by
  sorry

/-- Question 1: Can avoiding sets be substantially larger than N/2? -/
def erdos_327_question1 : Prop :=
  ∃ c : ℝ, c > 1/2 ∧ ∃ᶠ N : ℕ in atTop,
    ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ a ≤ N) ∧
      AvoidUnitFractionSums A ∧ (A.card : ℝ) > c * N

/-- Question 2: With condition a+b ∤ 2ab, must |A| = o(N)? -/
def erdos_327_question2 : Prop :=
  ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
    (∀ a ∈ A, 0 < a ∧ a ≤ N) →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬((a + b) ∣ (2 * a * b))) →
    (A.card : ℝ) < ε * N

end Erdos327
