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
# Erdős Problem 732

Block-compatible sequences count.

PROVED

*Reference:* [erdosproblems.com/732](https://www.erdosproblems.com/732)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos732

/-- Block-compatible sequence -/
def BlockCompatible (X : List ℕ) (n : ℕ) : Prop := sorry

/-- Number of block-compatible sequences -/
noncomputable def numBlockCompatible (n : ℕ) : ℕ := sorry

/-- Exponential lower bound for block-compatible sequences -/
@[category research solved, AMS 05]
theorem block_compatible_exponential_bound :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        numBlockCompatible n ≥ Real.exp (c * (n : ℝ) ^ (1/2 : ℝ) * Real.log n) := by
  sorry

end Erdos732
