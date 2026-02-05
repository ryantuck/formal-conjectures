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
# Erdős Problem 382

Let $u \leq v$ satisfy: the largest prime dividing $\prod_{u \leq m \leq v} m$ appears
with exponent at least 2.

Question 1: Is it true that $v - u = v^{o(1)}$?
Question 2: Can $v - u$ be arbitrarily large?

Ramachandra: $v - u \leq v^{1/2+o(1)}$.
Cambie: Question 1 reduces to Cramér's conjecture; heuristically Question 2 is yes.

*Reference:* [erdosproblems.com/382](https://www.erdosproblems.com/382)
-/

open Filter Topology BigOperators Real

namespace Erdos382

/-- Largest prime factor of n -/
noncomputable def P (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ p ∣ n}

/-- Condition that largest prime in product appears with exponent ≥ 2 -/
def SatisfiesCondition (u v : ℕ) : Prop :=
  u ≤ v ∧ ∃ p : ℕ, p.Prime ∧
    (p = P ((Finset.Ico u (v + 1)).prod id)) ∧
    p^2 ∣ ((Finset.Ico u (v + 1)).prod id)

/-- Ramachandra: v - u ≤ v^(1/2+o(1)) -/
@[category research open, AMS 11]
theorem erdos_382_ramachandra :
    ∀ ε > 0, ∀ᶠ v : ℕ in atTop, ∀ u : ℕ,
      SatisfiesCondition u v → (v - u : ℝ) ≤ (v : ℝ) ^ ((1:ℝ)/2 + ε) := by
  sorry

/-- Question 1: Does v - u = v^(o(1))? -/
def erdos_382_question1 : Prop :=
  ∀ ε > 0, ∀ᶠ v : ℕ in atTop, ∀ u : ℕ,
    SatisfiesCondition u v → (v - u : ℝ) < (v : ℝ) ^ ε

end Erdos382
