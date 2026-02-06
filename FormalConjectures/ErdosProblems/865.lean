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
# Erdős Problem 865

|A| ≥ (5/8)N+C implies three pairwise sums.

OPEN

*Reference:* [erdosproblems.com/865](https://www.erdosproblems.com/865)
-/

open Finset

open scoped Topology Real

namespace Erdos865

/-- Large set has three elements with all pairwise sums in set -/
@[category research open, AMS 11]
theorem large_set_three_pairwise_sums (N C : ℕ) (answer : Prop) :
    answer ↔ ∀ (A : Finset ℕ),
      A ⊆ Finset.range (N + 1) →
      A.card ≥ (5 * N) / 8 + C →
      ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A := by
  sorry

end Erdos865
