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
# Erdős Problem 538

Let r ≥ 2 and suppose A ⊆ {1,...,N} satisfies: for any m, there are at most r
solutions to m = pa where p is prime and a ∈ A. What is the best upper bound for ∑_{n∈A} 1/n?

Known: Erdős showed ∑_{n∈A} 1/n ≪ r log N / log log N.

OPEN

*Reference:* [erdosproblems.com/538](https://www.erdosproblems.com/538)
-/

open Real Finset Nat Classical

namespace Erdos538

/-- Erdős upper bound for reciprocal sum under prime constraint -/
@[category research open, AMS 11]
theorem reciprocal_sum_bound (r : ℕ) (hr : r ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 3 → ∀ (A : Finset ℕ),
      (∀ n ∈ A, 0 < n ∧ n ≤ N) →
      (∀ m : ℕ, (A.filter (fun a => ∃ p, p.Prime ∧ m = p * a)).card ≤ r) →
      ∑ n ∈ A, (1 : ℝ) / n ≤ C * r * Real.log N / Real.log (Real.log N) := by
  sorry

/-- Determine the optimal bound -/
@[category research open, AMS 11]
theorem optimal_reciprocal_bound :
    answer(sorry) ↔
      ∃ f : ℕ → ℕ → ℝ, ∀ r N, r ≥ 2 → N ≥ 3 →
        (∀ (A : Finset ℕ),
          (∀ n ∈ A, 0 < n ∧ n ≤ N) →
          (∀ m : ℕ, (A.filter (fun a => ∃ p, p.Prime ∧ m = p * a)).card ≤ r) →
          ∑ n ∈ A, (1 : ℝ) / n ≤ f r N) ∧
        (∃ (A : Finset ℕ),
          (∀ n ∈ A, 0 < n ∧ n ≤ N) ∧
          (∀ m : ℕ, (A.filter (fun a => ∃ p, p.Prime ∧ m = p * a)).card ≤ r) ∧
          ∑ n ∈ A, (1 : ℝ) / n ≥ f r N / 2) := by
  sorry

end Erdos538
