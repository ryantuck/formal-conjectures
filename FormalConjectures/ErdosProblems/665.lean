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
# Erdős Problem 665

Does there exist constant C > 0 such that for all large n, a pairwise balanced design
for {1,...,n} exists with all block sizes > n^(1/2) - C?

OPEN (problem of Erdős and Larson)

*Reference:* [erdosproblems.com/665](https://www.erdosproblems.com/665)
-/

open Finset

open scoped Topology Real

namespace Erdos665

/-- Pairwise balanced design exists with large block sizes -/
@[category research open, AMS 05]
theorem pairwise_balanced_design_large_blocks (answer : Prop) :
    answer ↔ ∃ C : ℝ, C > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ (blocks : Finset (Finset (Fin n))),
        sorry ∧  -- pairwise balanced condition
        ∀ B ∈ blocks, B.card > Nat.floor (Real.sqrt n - C) := by
  sorry

end Erdos665
