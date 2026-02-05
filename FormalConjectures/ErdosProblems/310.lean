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
# Erdős Problem 310

Let $\alpha > 0$ and $N \geq 1$. For any subset $A \subseteq \{1,\ldots,N\}$ with $|A| \geq \alpha N$,
does there exist some $S \subseteq A$ such that $\frac{a}{b} = \sum_{n \in S} \frac{1}{n}$
with $a \leq b = O_\alpha(1)$?

Liu and Sawhney showed this is true, and proved that when $(log N)^{-1/7+o(1)} \leq \alpha \leq 1/2$,
there exists $S \subseteq A$ with $b \leq \exp(O(1/\alpha))$, and this dependence is sharp.

*Reference:* [erdosproblems.com/310](https://www.erdosproblems.com/310)
-/

open Filter Topology BigOperators Real

namespace Erdos310

/-- For dense subsets of {1,...,N}, unit fraction sums can represent small fractions -/
@[category research solved, AMS 11]
theorem erdos_310 :
    ∀ α > 0, ∃ B : ℕ → ℕ, (∀ᶠ N in atTop, ∀ A : Finset ℕ,
      (∀ n ∈ A, 0 < n ∧ n ≤ N) →
      A.card ≥ α * N →
      ∃ S : Finset ℕ, S ⊆ A ∧
        ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ B N ∧
          (a : ℚ) / b = S.sum (fun n => (1 : ℚ) / n)) := by
  sorry

/-- Liu-Sawhney: Sharp bound for intermediate density range -/
@[category research solved, AMS 11]
theorem erdos_310_liu_sawhney :
    ∀ᶠ N in atTop, ∀ α : ℝ,
      (log N)^(-(1:ℝ)/7) ≤ α →
      α ≤ 1/2 →
      ∀ A : Finset ℕ,
        (∀ n ∈ A, 0 < n ∧ n ≤ N) →
        (A.card : ℝ) ≥ α * N →
        ∃ S : Finset ℕ, S ⊆ A ∧
          ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧
            (b : ℝ) ≤ exp (10 / α) ∧
            (a : ℚ) / b = S.sum (fun n => (1 : ℚ) / n) := by
  sorry

end Erdos310
