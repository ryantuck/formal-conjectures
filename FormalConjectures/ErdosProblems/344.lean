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
# Erdős Problem 344

If a set A ⊆ ℕ satisfies |A ∩ {1,...,N}| ≫ N^(1/2) for all N, must A be subcomplete?
That is, must the sumset P(A) contain an infinite arithmetic progression?

PROVED: Solved affirmatively by Szemerédi and Vu.

Related results:
- Folkman: Established the result under |A ∩ {1,...,N}| ≫ N^(1/2+ε) for some ε > 0.
- Open stronger conjecture: The result holds under |A ∩ {1,...,N}| ≥ (2N)^(1/2),
  which would be optimal.

*Reference:* [erdosproblems.com/344](https://www.erdosproblems.com/344)
-/

open Filter Topology BigOperators Real

namespace Erdos344

/-- The set of subset sums -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.sum id = n}

/-- A set is subcomplete if it contains an infinite arithmetic progression -/
def IsSubcomplete (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ k : ℕ, a + k * d ∈ S

/-- Szemerédi-Vu: Sets with density N^(1/2) are subcomplete -/
@[category research solved, AMS 11]
theorem erdos_344_szemeredi_vu :
    ∀ A : Set ℕ, (∃ c > 0, ∀ N : ℕ, (Nat.card {n ∈ A | n ≤ N} : ℝ) ≥ c * (N : ℝ)^(1/2 : ℝ)) →
      IsSubcomplete (subsetSums A) := by
  sorry

/-- Folkman: Result for N^(1/2+ε) -/
@[category research solved, AMS 11]
theorem erdos_344_folkman (ε : ℝ) (hε : ε > 0) :
    ∀ A : Set ℕ, (∃ c > 0, ∀ N : ℕ, (Nat.card {n ∈ A | n ≤ N} : ℝ) ≥ c * N^(1/2 + ε)) →
      IsSubcomplete (subsetSums A) := by
  sorry

/-- Open stronger conjecture: (2N)^(1/2) threshold -/
@[category research open, AMS 11]
theorem erdos_344_optimal :
    ∀ A : Set ℕ, (∀ N : ℕ, (Nat.card {n ∈ A | n ≤ N} : ℝ) ≥ (2 * N)^(1/2 : ℝ)) →
      IsSubcomplete (subsetSums A) := by
  sorry

end Erdos344
