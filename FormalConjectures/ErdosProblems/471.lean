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
# Erdős Problem 471

Given a finite set of primes Q₀, define Qᵢ₊₁ as Qᵢ together with all primes formed by
adding three distinct elements of Qᵢ. Does there exist Q₀ such that the Qᵢ become
arbitrarily large?

Mrazović-Kovač and Alon: PROVED - Using Vinogradov's theorem, taking Q₀ as all primes
≤ N for sufficiently large N ensures all primes eventually appear.

*Reference:* [erdosproblems.com/471](https://www.erdosproblems.com/471)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos471

/-- The iterative prime generation sequence -/
noncomputable def Q : Set ℕ → ℕ → Set ℕ
  | Q0, 0 => Q0
  | Q0, n + 1 => Q Q0 n ∪ {p : ℕ | p.Prime ∧
      ∃ a ∈ Q Q0 n, ∃ b ∈ Q Q0 n, ∃ c ∈ Q Q0 n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ p = a + b + c}

/-- Mrazović-Kovač-Alon: Q becomes arbitrarily large -/
@[category research solved, AMS 11]
theorem erdos_471 :
    ∃ Q0 : Set ℕ, Q0.Finite ∧ (∀ p ∈ Q0, p.Prime) ∧
      ∀ M : ℕ, ∃ n : ℕ, M ≤ (Q Q0 n).ncard := by
  sorry

end Erdos471
