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
# Erdős Problem 663

For fixed k ≥ 2, let q(n,k) be the least prime not dividing ∏_{1≤i≤k}(n+i).
Is q(n,k) < (1+o(1))log n for large n?

OPEN (problem of Erdős and Pomerance)

*Reference:* [erdosproblems.com/663](https://www.erdosproblems.com/663)
-/

open Nat

open scoped Topology Real

namespace Erdos663

/-- q(n,k): least prime not dividing product -/
noncomputable def q (n k : ℕ) : ℕ := sorry

/-- Is q(n,k) < (1+o(1))log n? -/
@[category research open, AMS 11]
theorem least_prime_not_dividing_product (k : ℕ) (hk : k ≥ 2) (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      (q n k : ℝ) < (1 + ε) * Real.log n := by
  sorry

end Erdos663
