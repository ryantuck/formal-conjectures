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
# Erdős Problem 818

Sum-product for small sumset.

SOLVED

*Reference:* [erdosproblems.com/818](https://www.erdosproblems.com/818)
-/

open Finset

open scoped Topology Real

namespace Erdos818

/-- If |A+A| ≪ |A| then |AA| ≫ |A|²/log |A| -/
@[category research solved, AMS 11]
theorem sum_product_small_sumset :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∀ (A : Finset ℤ) (sumA : Finset ℤ) (prodA : Finset ℤ),
        (∀ s ∈ sumA, ∃ a ∈ A, ∃ b ∈ A, a + b = s) →
        (∀ p ∈ prodA, ∃ a ∈ A, ∃ b ∈ A, a * b = p) →
        (sumA.card : ℝ) ≤ C * A.card →
        (prodA.card : ℝ) ≥ c * (A.card : ℝ) ^ 2 / Real.log A.card := by
  sorry

end Erdos818
