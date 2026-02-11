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
# Erdős Problem 1109

Squarefree sumsets.

OPEN

*Reference:* [erdosproblems.com/1109](https://www.erdosproblems.com/1109)
-/

open Finset

open scoped Real

namespace Erdos1109

/-- Squarefree sumsets property.
    Asks about sets A, B where A+B consists only of squarefree numbers, with positive density. -/
@[category research open, AMS 11]
theorem squarefree_sumsets :
    ∃ (A B : Set ℕ), (∀ a ∈ A, ∀ b ∈ B, Squarefree (a + b)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop,
        ((A ∩ Set.Icc 1 n).ncard : ℝ) / n ≥ c) := by
  sorry

end Erdos1109
