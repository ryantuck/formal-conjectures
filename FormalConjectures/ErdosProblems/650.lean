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
# Erdős Problem 650

Estimate f(m) for divisibility in intervals; is f(m) ≪ m^(1/2)?

OPEN

*Reference:* [erdosproblems.com/650](https://www.erdosproblems.com/650)
-/

open Nat

open scoped Topology Real

namespace Erdos650

/-- f(m) for divisibility in intervals -/
noncomputable def f (m : ℕ) : ℕ := sorry

/-- Is f(m) ≪ m^(1/2)? -/
@[category research open, AMS 11]
theorem divisibility_intervals (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (m : ℕ) in Filter.atTop,
      (f m : ℝ) < (m : ℝ) ^ (1/2 + ε) := by
  sorry

end Erdos650
