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
# Erdős Problem 708

Determine bounds for g(n) - minimal value for product divisibility.

OPEN ($100 reward)

*Reference:* [erdosproblems.com/708](https://www.erdosproblems.com/708)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos708

/-- g(n): minimal value for product divisibility -/
noncomputable def g (n : ℕ) : ℕ := sorry

/-- Conjecture: g(n) ≤ (2+o(1))n or even g(n) ≤ 2n -/
@[category research open, AMS 11]
theorem product_divisibility_bound (answer : Prop) :
    answer ↔ ∀ᶠ (n : ℕ) in Filter.atTop, g n ≤ 2 * n := by
  sorry

end Erdos708
