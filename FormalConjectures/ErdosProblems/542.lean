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
# Erdős Problem 542

Let A ⊆ {1,...,n} where lcm(a,b) > n for all distinct a,b ∈ A.
(1) Must ∑_{a∈A} 1/a ≤ 31/30?
(2) Must there be ≫ n integers m ≤ n not dividing any element of A?

SOLVED: Schinzel-Szekeres answered yes to (1), no to (2).
The bound 31/30 is tight (achieved by {2,3,5}).

*Reference:* [erdosproblems.com/542](https://www.erdosproblems.com/542)
-/

open Nat Finset Real

namespace Erdos542

/-- Reciprocal sum bound for LCM-constrained sets -/
@[category research solved, AMS 11]
theorem reciprocal_sum_lcm_bound (n : ℕ) (hn : n > 0) :
    ∀ (A : Finset ℕ),
      (∀ a ∈ A, 0 < a ∧ a ≤ n) →
      (∀ a b, a ∈ A → b ∈ A → a ≠ b → Nat.lcm a b > n) →
      ∑ a ∈ A, (1 : ℝ) / a ≤ 31 / 30 := by
  sorry

/-- The bound 31/30 is tight -/
@[category research solved, AMS 11]
theorem reciprocal_sum_bound_tight :
    ∃ (A : Finset ℕ) (n : ℕ), n > 0 ∧
      (∀ a ∈ A, 0 < a ∧ a ≤ n) ∧
      (∀ a b, a ∈ A → b ∈ A → a ≠ b → Nat.lcm a b > n) ∧
      ∑ a ∈ A, (1 : ℝ) / a = 31 / 30 := by
  sorry

/-- Counterexample: not many non-divisors guaranteed -/
@[category research solved, AMS 11]
theorem non_divisors_counterexample :
    ∀ ε : ℝ, ε > 0 → ∃ c > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ (A : Finset ℕ),
        (∀ a ∈ A, 0 < a ∧ a ≤ n) ∧
        (∀ a b, a ∈ A → b ∈ A → a ≠ b → Nat.lcm a b > n) ∧
        ((Finset.range (n + 1)).filter (fun m =>
          m > 0 ∧ ∀ a ∈ A, ¬(a ∣ m))).card ≤ ⌊n / (Real.log n) ^ c⌋₊ := by
  sorry

end Erdos542
