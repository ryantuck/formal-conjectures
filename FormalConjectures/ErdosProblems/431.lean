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
# Erdős Problem 431

Are there two infinite sets A and B such that A+B agrees with the set of prime numbers
up to finitely many exceptions?

Known as the inverse Goldbach problem (Ostmann). Consensus: answer is "no."

Elsholtz-Harper (2015): If such sets exist, then for all large x:
  x^(1/2) / (log x log log x) ≪ |A ∩ [1,x]| ≪ x^(1/2) log log x

Elsholtz (2001): No three sets A,B,C exist such that A+B+C equals the primes
up to finitely many exceptions.

*Reference:* [erdosproblems.com/431](https://www.erdosproblems.com/431)
-/

open Filter Topology BigOperators Real

namespace Erdos431

/-- Inverse Goldbach: No two sets sum to primes (conjectured) -/
@[category research open, AMS 11]
theorem erdos_431_inverse_goldbach :
    ¬∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      Set.Finite (({p : ℕ | p.Prime} \ {s : ℕ | ∃ a ∈ A, ∃ b ∈ B, s = a + b}) ∪
        ({s : ℕ | ∃ a ∈ A, ∃ b ∈ B, s = a + b} \ {p : ℕ | p.Prime})) := by
  sorry

/-- Elsholtz-Harper: Bounds if such sets exist -/
@[category research open, AMS 11]
theorem erdos_431_elsholtz_harper :
    (∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      Set.Finite (({p : ℕ | p.Prime} \ {s : ℕ | ∃ a ∈ A, ∃ b ∈ B, s = a + b}) ∪
        ({s : ℕ | ∃ a ∈ A, ∃ b ∈ B, s = a + b} \ {p : ℕ | p.Prime}))) →
    ∀ A B : Set ℕ, A.Infinite ∧ B.Infinite →
      Set.Finite (({p : ℕ | p.Prime} \ {s : ℕ | ∃ a ∈ A, ∃ b ∈ B, s = a + b}) ∪
        ({s : ℕ | ∃ a ∈ A, ∃ b ∈ B, s = a + b} \ {p : ℕ | p.Prime})) →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ x : ℝ in atTop,
        c₁ * x^((1:ℝ)/2) / (log x * log (log x)) ≤
          (Nat.card {a ∈ A | (a : ℝ) ≤ x} : ℝ) ∧
        (Nat.card {a ∈ A | (a : ℝ) ≤ x} : ℝ) ≤
          c₂ * x^((1:ℝ)/2) * log (log x) := by
  sorry

/-- Elsholtz: No three sets sum to primes -/
@[category research solved, AMS 11]
theorem erdos_431_elsholtz_three_sets :
    ¬∃ A B C : Set ℕ, (A.ncard ≥ 2) ∧ (B.ncard ≥ 2) ∧ (C.ncard ≥ 2) ∧
      Set.Finite (({p : ℕ | p.Prime} \ {s : ℕ | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, s = a + b + c}) ∪
        ({s : ℕ | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, s = a + b + c} \ {p : ℕ | p.Prime})) := by
  sorry

end Erdos431
