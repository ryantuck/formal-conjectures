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
# Erdős Problem 337

Let $A \subseteq \mathbb{N}$ be an additive basis of any finite order such that $|A \cap \{1,\ldots,N\}| = o(N)$.
Is it true that $\lim_{N\to \infty} |A+A \cap \{1,\ldots,N\}| / |A \cap \{1,\ldots,N\}| = \infty$?

DISPROVED: Turjányi provided a counterexample.

However, Ruzsa-Turjányi proved: $\lim |A+A+A \cap \{1,\ldots,3N\}| / |A \cap \{1,\ldots,N\}| = \infty$.

*Reference:* [erdosproblems.com/337](https://www.erdosproblems.com/337)
-/

open Filter Topology BigOperators Real

namespace Erdos337

/-- A is an additive basis of order r if every large n is an r-fold sum from A -/
def IsAdditiveBasis (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card ≤ r ∧ S.sum id = n

/-- The h-fold sumset -/
def hFoldSum (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card = h ∧ S.sum id = n}

/-- Turjányi disproved the original question -/
@[category research solved, AMS 11]
theorem erdos_337_disproved :
    ¬∀ A : Set ℕ, (∃ r : ℕ, IsAdditiveBasis A r) →
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, (Nat.card {n ∈ A | n ≤ N} : ℝ) < ε * N) →
      Tendsto (fun N => (Nat.card {n ∈ hFoldSum A 2 | n ≤ N} : ℝ) /
        (Nat.card {n ∈ A | n ≤ N})) atTop atTop := by
  sorry

/-- Ruzsa-Turjányi: The 3-fold sumset does grow -/
@[category research solved, AMS 11]
theorem erdos_337_ruzsa_turjanyi :
    ∀ A : Set ℕ, (∃ r : ℕ, IsAdditiveBasis A r) →
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, (Nat.card {n ∈ A | n ≤ N} : ℝ) < ε * N) →
      Tendsto (fun N => (Nat.card {n ∈ hFoldSum A 3 | n ≤ 3*N} : ℝ) /
        (Nat.card {n ∈ A | n ≤ N})) atTop atTop := by
  sorry

end Erdos337
