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
# Erdős Problem 1136

Sumset-free sets with high lower density.

PROVED

*Reference:* [erdosproblems.com/1136](https://www.erdosproblems.com/1136)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1136

/-- Sumset-free sets avoiding powers of 2 -/
@[category research solved, AMS 11]
theorem sumset_free_high_density :
    ∃ (A : Set ℕ),
      (∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2^k) ∧
      liminf (fun X => (A ∩ Set.Icc 1 X).ncard / X) atTop > 1/3 := by
  sorry

end Erdos1136
