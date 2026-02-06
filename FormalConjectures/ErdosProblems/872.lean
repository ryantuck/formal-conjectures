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
# Erdős Problem 872

Divisibility-free selection game.

OPEN

*Reference:* [erdosproblems.com/872](https://www.erdosproblems.com/872)
-/

open Finset

open scoped Topology Real

namespace Erdos872

/-- Game length for divisibility-free selection -/
@[category research open, AMS 11]
theorem divisibility_game (answer : Prop) :
    answer ↔ ∃ ε : ℝ, ε > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        sorry := by
  sorry

end Erdos872
