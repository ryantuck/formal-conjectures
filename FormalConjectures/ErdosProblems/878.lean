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
# Erdős Problem 878

Number-theoretic functions f(n) and F(n).

OPEN

*Reference:* [erdosproblems.com/878](https://www.erdosproblems.com/878)
-/

open Finset Nat Filter Asymptotics

open scoped Topology Real

namespace Erdos878

/-- f(n) = ∑ pᵢ^ℓᵢ where n ∈ [pᵢ^ℓᵢ, pᵢ^{ℓᵢ+1}) for each prime factor pᵢ -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ (Nat.log p n)

/-- F(n) = max ∑ aᵢ where aᵢ ≤ n are pairwise coprime and all primes dividing aᵢ divide n -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset ℕ, (∀ a ∈ S, a ≤ n) ∧
    (∀ a b, a ∈ S → b ∈ S → a ≠ b → Nat.Coprime a b) ∧
    (∀ a ∈ S, ∀ p : ℕ, p.Prime → p ∣ a → p ∣ n) ∧
    k = ∑ a ∈ S, a}

/-- Question 1: For almost all n, f(n) = o(n log log n) and F(n) ≫ n log log n -/
@[category research open, AMS 11]
theorem f_small_F_large :
    (∀ ε > 0, ∀ᶠ n in atTop, (f n : ℝ) < ε * n * Real.log (Real.log n)) ∧
    (∃ C > 0, ∀ᶠ n in atTop, (F n : ℝ) > C * n * Real.log (Real.log n)) := by
  sorry

/-- Question 2: max_{n≤x} f(n) ~ x log x / log log x -/
@[category research open, AMS 11]
theorem max_f_asymptotic :
    (fun x => sSup {(f n : ℝ) | n ≤ x}) ~[atTop]
    (fun x => x * Real.log x / Real.log (Real.log x)) := by
  sorry

/-- Question 3: max_{n≤x} f(n) = max_{n≤x} F(n) for all large x -/
@[category research open, AMS 11]
theorem max_f_equals_max_F :
    ∀ᶠ x in atTop, sSup {f n | n ≤ x} = sSup {F n | n ≤ x} := by
  sorry

/-- Question 5: Asymptotic formula for H(x) = ∑_{n<x} f(n)/n -/
@[category research open, AMS 11]
theorem H_asymptotic :
    ∃ g : ℝ → ℝ, (fun x => ∑ n ∈ Finset.range ⌊x⌋₊, (f n : ℝ) / n) ~[atTop] g := by
  sorry

/-- Question 6: H(x) ≪ x log log log log x -/
@[category research open, AMS 11]
theorem H_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ x : ℝ, x ≥ 2 →
      (∑ n ∈ Finset.range ⌊x⌋₊, (f n : ℝ) / n) ≤
      C * x * Real.log (Real.log (Real.log (Real.log x))) := by
  sorry

end Erdos878
