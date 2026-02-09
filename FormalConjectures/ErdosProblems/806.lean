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
# Erdős Problem 806

Small set contained in sumset.

PROVED

*Reference:* [erdosproblems.com/806](https://www.erdosproblems.com/806)
-/

open Finset

open scoped Topology Real

namespace Erdos806

/-- Small set in sumset of smaller set -/
@[category research solved, AMS 11]
theorem small_set_in_sumset :
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.range (n + 1) →
      A.card ≤ (n : ℝ) ^ (1/2 : ℝ) →
      ∃ (B : Finset ℕ),
        (∀ a ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ + b₂ = a) ∧
        B.card ≤ A.card := by
  sorry

end Erdos806
