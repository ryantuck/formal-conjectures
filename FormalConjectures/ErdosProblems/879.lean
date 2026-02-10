/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 879

Admissible sets - maximum sum G(n).

OPEN

*Reference:* [erdosproblems.com/879](https://www.erdosproblems.com/879)
-/

open Finset Nat Filter

open scoped Topology Real BigOperators

namespace Erdos879

/-- Admissible set (pairwise coprime) -/
def IsAdmissible (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → Nat.Coprime a b

/-- G(n): maximum sum of admissible subset of {1,...,n} -/
noncomputable def G (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, (∀ a ∈ A, a ≤ n) ∧ IsAdmissible A ∧ k = ∑ a ∈ A, a}

/-- H(n) = (sum of primes < n) + n·π(√n) -/
noncomputable def H (n : ℕ) : ℕ :=
  (∑ p ∈ Finset.range n, if Nat.Prime p then p else 0) +
  n * ((Finset.range n).filter (fun p => Nat.Prime p ∧ p * p ≤ n)).card

/-- Erdős-Van Lint bounds: H(n) - n^{3/2-o(1)} < G(n) < H(n) -/
@[category research solved, AMS 11]
theorem erdos_van_lint_bounds :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (H n : ℝ) - (n : ℝ) ^ (3/2 - ε) < G n ∧ G n < H n := by
  sorry

/-- Question 1: G(n) > H(n) - n^{1+o(1)} -/
@[category research open, AMS 11]
theorem G_close_to_H :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (G n : ℝ) > (H n : ℝ) - (n : ℝ) ^ (1 + ε) := by
  sorry

/-- Question 2: For k ≥ 2, the set maximizing G(n) contains an integer
    with ≥ k prime factors for large n -/
@[category research open, AMS 11]
theorem max_set_has_k_prime_factors (k : ℕ) (hk : k ≥ 2) :
    ∀ᶠ n in Filter.atTop, ∃ A : Finset ℕ,
      (∀ a ∈ A, a ≤ n) ∧ IsAdmissible A ∧ (∑ a ∈ A, a) = G n ∧
      ∃ a ∈ A, (a.primeFactors.card ≥ k) := by
  sorry

/-- Known for k=2: maximizing set contains composite number -/
@[category research solved, AMS 11]
theorem max_set_has_composite :
    ∀ᶠ n in Filter.atTop, ∃ A : Finset ℕ,
      (∀ a ∈ A, a ≤ n) ∧ IsAdmissible A ∧ (∑ a ∈ A, a) = G n ∧
      ∃ a ∈ A, ¬a.Prime ∧ a > 1 := by
  sorry

end Erdos879
