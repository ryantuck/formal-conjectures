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
# Erdős Problem 343

If A ⊆ ℕ is a multiset of integers such that |A ∩ {1,...,N}| ≫ N for all N, must A be
subcomplete? That is, must the set of subset sums P(A) contain an infinite arithmetic
progression?

PROVED: Answered affirmatively by Szemerédi and Vu (2006).

Prior work:
- Folkman (1966): Proved for |A ∩ {1,...,N}| ≫ N^(1+ε) for some ε > 0.
- Folkman also showed this is best possible by constructing counterexamples with
  |A ∩ {1,...,N}| ≫ N^(1-ε) that are not subcomplete.

*Reference:* [erdosproblems.com/343](https://www.erdosproblems.com/343)
-/

open Filter Topology BigOperators Real

namespace Erdos343

/-- The set of subset sums (power set sums) -/
def subsetSums (A : Multiset ℕ) : Set ℕ :=
  {n : ℕ | ∃ B : Multiset ℕ, B ≤ A ∧ B.sum = n}

/-- A set is subcomplete if it contains an infinite arithmetic progression -/
def IsSubcomplete (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ k : ℕ, a + k * d ∈ S

/-- Szemerédi-Vu: Dense multisets are subcomplete -/
@[category research solved, AMS 11]
theorem erdos_343_szemeredi_vu :
    ∀ A : Multiset ℕ, (∃ c > 0, ∀ N : ℕ, ((A.filter (· ≤ N)).card : ℝ) ≥ c * N) →
      IsSubcomplete (subsetSums A) := by
  sorry

/-- Folkman: Stronger density condition -/
@[category research solved, AMS 11]
theorem erdos_343_folkman (ε : ℝ) (hε : ε > 0) :
    ∀ A : Multiset ℕ, (∃ c > 0, ∀ N : ℕ, ((A.filter (· ≤ N)).card : ℝ) ≥ c * (N : ℝ)^(1 + ε)) →
      IsSubcomplete (subsetSums A) := by
  sorry

/-- Folkman: Optimality (weaker density not sufficient) -/
@[category research solved, AMS 11]
theorem erdos_343_folkman_optimal (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    ∃ A : Multiset ℕ, (∃ c > 0, ∀ N : ℕ, ((A.filter (· ≤ N)).card : ℝ) ≥ c * (N : ℝ)^(1 - ε)) ∧
      ¬IsSubcomplete (subsetSums A) := by
  sorry

end Erdos343
