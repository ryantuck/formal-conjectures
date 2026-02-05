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
# Erdős Problem 534

What is the largest possible subset A ⊆ {1,...,N} containing N such that
gcd(a,b) > 1 for all distinct a,b ∈ A?

SOLVED: Ahlswede-Khachatrian proved the refined Erdős conjecture.

*Reference:* [erdosproblems.com/534](https://www.erdosproblems.com/534)
-/

open Nat Finset

namespace Erdos534

/-- A set is coprime-free if any two distinct elements share a common factor -/
def IsCoprimeFree (A : Finset ℕ) : Prop :=
  ∀ a b, a ∈ A → b ∈ A → a ≠ b → Nat.gcd a b > 1

/-- Maximum coprime-free subset of {1,...,N} containing N -/
noncomputable def maxCoprimeFree (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (A : Finset ℕ),
    (∀ n ∈ A, n ≤ N) ∧ N ∈ A ∧ IsCoprimeFree A ∧ A.card = k}

/-- The Ahlswede-Khachatrian theorem -/
@[category research solved, AMS 11]
theorem ahlswede_khachatrian :
    ∀ N : ℕ, N > 1 →
      ∃ (A : Finset ℕ), (∀ n ∈ A, n ≤ N) ∧ N ∈ A ∧
        IsCoprimeFree A ∧ A.card = maxCoprimeFree N ∧
        ∃ (divisors : Finset ℕ),
          (∀ d ∈ divisors, d > 0) ∧
          A = (Finset.range (N + 1)).filter (fun n =>
            ∃ d ∈ divisors, d ∣ n) := by
  sorry

end Erdos534
