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
# Erdős Problem 537

Let ε > 0 and N sufficiently large. If A ⊆ {1,...,N} has |A| ≥ εN, must there exist
a₁, a₂, a₃ ∈ A and distinct primes p₁, p₂, p₃ such that a₁p₁ = a₂p₂ = a₃p₃?

DISPROVED: Ruzsa constructed a counterexample using squarefree numbers.

*Reference:* [erdosproblems.com/537](https://www.erdosproblems.com/537)
-/

open Nat Finset

namespace Erdos537

/-- Disproof: dense sets need not have the triple prime product property -/
@[category research solved, AMS 11]
theorem ruzsa_counterexample :
    answer(False) ↔
      ∀ ε : ℝ, ε > 0 → ∀ N : ℕ, ∃ (A : Finset ℕ),
        (∀ n ∈ A, 0 < n ∧ n ≤ N) ∧ A.card ≥ ⌊ε * N⌋₊ ∧
        ∀ a₁ a₂ a₃ p₁ p₂ p₃,
          a₁ ∈ A → a₂ ∈ A → a₃ ∈ A →
          p₁.Prime → p₂.Prime → p₃.Prime →
          p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ →
          ¬(a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃) := by
  sorry

/-- Ruzsa's construction uses squarefree numbers with growing prime gaps -/
@[category research solved, AMS 11]
theorem ruzsa_construction_exists :
    ∃ ε : ℝ, ε > 0 ∧ ∃ (A : Set ℕ),
      (∃ d : ℝ, d ≥ ε ∧ ∀ᶠ N in Filter.atTop,
        ((A ∩ Set.Icc 1 N).ncard : ℝ) / N ≥ d) ∧
      (∀ n ∈ A, Squarefree n) ∧
      ∀ a₁ a₂ a₃ p₁ p₂ p₃,
        a₁ ∈ A → a₂ ∈ A → a₃ ∈ A →
        p₁.Prime → p₂.Prime → p₃.Prime →
        p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ →
        ¬(a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃) := by
  sorry

end Erdos537
