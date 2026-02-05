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
# Erdős Problem 362

Let $A \subseteq \mathbb{N}$ be a finite set of size $N$.

Question 1: For any fixed target sum $t$, is the number of subsets $S \subseteq A$
satisfying $\sum_{n \in S} n = t$ bounded by $\ll \frac{2^N}{N^{3/2}}$?

Question 2: If additionally $|S| = l$, is the number of solutions $\ll \frac{2^N}{N^2}$?

Erdős-Moser proved question 1 with extra $(\\log N)^{3/2}$ factor.
Sárközy-Szemerédi removed this factor. Halász resolved question 2.

*Reference:* [erdosproblems.com/362](https://www.erdosproblems.com/362)
-/

open Filter Topology BigOperators Real

namespace Erdos362

/-- Sárközy-Szemerédi: Number of subsets with given sum -/
@[category research solved, AMS 11]
theorem erdos_362_sarkozy_szemeredi :
    ∃ C : ℝ, C > 0 ∧ ∀ A : Finset ℕ, ∀ t : ℕ,
      (Nat.card {S : Finset ℕ | S ⊆ A ∧ S.sum id = t} : ℝ) ≤
        C * 2^A.card / (A.card : ℝ)^((3:ℝ)/2) := by
  sorry

/-- Halász: Number of size-l subsets with given sum -/
@[category research solved, AMS 11]
theorem erdos_362_halasz :
    ∃ C : ℝ, C > 0 ∧ ∀ A : Finset ℕ, ∀ t l : ℕ,
      (Nat.card {S : Finset ℕ | S ⊆ A ∧ S.card = l ∧ S.sum id = t} : ℝ) ≤
        C * 2^A.card / (A.card : ℝ)^2 := by
  sorry

end Erdos362
