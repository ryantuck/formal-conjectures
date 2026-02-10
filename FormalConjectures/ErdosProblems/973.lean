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
# Erdős Problem 973

Complex power sum bounds.

OPEN

*Reference:* [erdosproblems.com/973](https://www.erdosproblems.com/973)
-/

open Finset

open scoped Topology Real

namespace Erdos973

/-- Power sum bounds for complex numbers -/
@[category research open, AMS 41]
theorem complex_power_sum_bounds (answer : Prop) :
    answer ↔ ∃ (C : ℝ), 1 < C ∧
      ∀ n ≥ 2, ∃ (z : Fin n → ℂ) (h0 : 0 < n),
        z ⟨0, h0⟩ = 1 ∧
        (∀ i : Fin n, 1 ≤ ‖z i‖) ∧
        ∀ k : ℕ, ‖∑ i : Fin n, (z i) ^ k‖ < C ^ (-(n : ℝ)) := by
  sorry

end Erdos973
