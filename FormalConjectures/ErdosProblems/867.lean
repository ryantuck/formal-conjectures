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
# Erdős Problem 867

Set avoiding consecutive sums bound.

DISPROVED

*Reference:* [erdosproblems.com/867](https://www.erdosproblems.com/867)
-/

open Finset

open scoped Topology Real

namespace Erdos867

/-- Set avoiding consecutive sums -/
@[category research solved, AMS 11]
theorem not_consecutive_sum_half (N : ℕ) :
    ¬ ∀ (A : Finset ℕ),
      A ⊆ Finset.range (N + 1) →
      (∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
        a < b → b < c → c < d →
        a + b + c ≠ d) →
      A.card ≤ N / 2 + sorry := by
  sorry

/-- Current bounds -/
@[category research solved, AMS 11]
theorem consecutive_sum_bounds (N : ℕ) :
    ∃ (A : Finset ℕ),
      A ⊆ Finset.range (N + 1) ∧
      sorry ∧
      A.card ≥ (13 * N) / 24 - sorry ∧
      A.card ≤ (2 / 3 - 1 / 512) * N + Real.log N := by
  sorry

end Erdos867
