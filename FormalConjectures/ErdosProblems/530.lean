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
# Erdős Problem 530

Let ℓ(N) denote the maximum size of a Sidon subset guaranteed in any finite set A ⊂ ℝ
with |A| = N. Determine the order of ℓ(N). Is it true that ℓ(N) ~ N^(1/2)?

Known: N^(1/2) ≪ ℓ(N) ≤ (1+o(1))N^(1/2) by Komlós-Sulyok-Szemerédi and Erdős.

OPEN

*Reference:* [erdosproblems.com/530](https://www.erdosproblems.com/530)
-/

open Real Finset

namespace Erdos530

/-- A set is Sidon if all pairwise sums are distinct (except trivial equalities) -/
def IsSidon (S : Finset ℝ) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Maximum Sidon subset size guaranteed in any N-element set -/
noncomputable def sidonGuarantee (N : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (A : Finset ℝ), A.card = N → ∃ (S : Finset ℝ), S ⊆ A ∧ IsSidon S ∧ S.card ≥ k}

/-- Sidon guarantee grows like √N -/
@[category research open, AMS 11]
theorem sidon_guarantee_sqrt :
    ∃ c > 0, ∀ᶠ N in Filter.atTop, sidonGuarantee N ≥ c * Real.sqrt N := by
  sorry

/-- Conjecture: Sidon guarantee is asymptotically √N -/
@[category research open, AMS 11]
theorem sidon_guarantee_asymptotic_conjecture :
    answer(sorry) ↔ ∃ c > 0, ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      |sidonGuarantee N / Real.sqrt N - c| < ε := by
  sorry

end Erdos530
