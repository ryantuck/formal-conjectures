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
# Erdős Problem 531

Let F(k) be the minimal N such that if we 2-color {1,...,N}, there exists a set A
of size k where all non-empty subset sums are monochromatic. Estimate F(k).

Known: 2^(2^(k-1)/k) ≤ F(k) by Balogh et al.

OPEN

*Reference:* [erdosproblems.com/531](https://www.erdosproblems.com/531)
-/

open Finset

namespace Erdos531

/-- Minimal N ensuring monochromatic subset sums for size k -/
noncomputable def F (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : ℕ → Fin 2), ∃ (A : Finset ℕ),
    A.card = k ∧ (∀ n ∈ A, n ≤ N) ∧
    ∃ col : Fin 2, ∀ (S : Finset ℕ), S ⊆ A → S.Nonempty →
      c (∑ n ∈ S, n) = col}

/-- Lower bound for F(k) -/
@[category research open, AMS 05 11]
theorem F_lower_bound :
    ∃ c > 0, ∀ k : ℕ, k ≥ 2 → F k ≥ 2 ^ ⌊(2 ^ (k - 1) / k : ℝ)⌋₊ := by
  sorry

/-- Estimate F(k) -/
@[category research open, AMS 05 11]
theorem estimate_F :
    answer(sorry) ↔ ∃ f : ℕ → ℝ, (∀ k, (F k : ℝ) = f k) ∧
      ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
        ∀ k, c₁ * 2 ^ (2 ^ k / k) ≤ f k ∧ f k ≤ c₂ * 2 ^ (2 ^ k / k) := by
  sorry

end Erdos531
