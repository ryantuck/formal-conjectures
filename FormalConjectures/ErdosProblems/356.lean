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
# Erdős Problem 356

Is there some c > 0 such that, for all sufficiently large n, there exist integers
a₁ < ... < aₖ ≤ n such that there are at least cn² distinct integers of the form
Σ_{u≤i≤v} aᵢ?

PROVED: Solved affirmatively by Beker (2023).

This fails for the natural sequence aᵢ = i. Without the monotonicity restriction,
Konieczny (2015) confirmed that some arrangement of {1,...,n} achieves cn² distinct
subsums.

*Reference:* [erdosproblems.com/356](https://www.erdosproblems.com/356)
-/

open Filter Topology BigOperators Real Finset

namespace Erdos356

/-- The number of distinct interval sums from a sequence -/
noncomputable def numDistinctIntervalSums {k : ℕ} (a : Fin k → ℤ) : ℕ :=
  Nat.card {s : ℤ | ∃ u v : Fin k, u ≤ v ∧ s = ∑ i ∈ Finset.Icc u v, a i}

/-- Beker: There exists c > 0 such that for large n, we can find a sequence with cn² distinct sums -/
@[category research solved, AMS 11]
theorem erdos_356_main :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, ∃ a : Fin k → ℤ,
      (∀ i j : Fin k, i < j → a i < a j) ∧
      (∀ i : Fin k, a i ≤ n) ∧
      (numDistinctIntervalSums a : ℝ) ≥ c * n^2 := by
  sorry

/-- Konieczny: Without monotonicity, some arrangement achieves cn² distinct subsums -/
@[category research solved, AMS 11]
theorem erdos_356_konieczny :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ a : Fin n → ℕ,
      (∀ i : Fin n, a i ∈ Finset.range (n + 1)) ∧
      (∀ i j : Fin n, a i = a j → i = j) ∧
      (numDistinctIntervalSums (fun i => (a i : ℤ)) : ℝ) ≥ c * n^2 := by
  sorry

end Erdos356
