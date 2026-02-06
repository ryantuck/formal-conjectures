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
# Erdős Problem 693

Estimate max gap in integers in [n, n^k] with divisors in (n, 2n).

OPEN

*Reference:* [erdosproblems.com/693](https://www.erdosproblems.com/693)
-/

open Nat

open scoped Topology Real

namespace Erdos693

/-- Max gap in integers with divisors in (n, 2n) -/
noncomputable def maxGap (n k : ℕ) : ℕ := sorry

/-- Estimate maxGap(n,k) -/
@[category research open, AMS 11]
theorem max_gap_divisors_in_range (k : ℕ) :
    ∃ f : ℕ → ℕ, ∀ n : ℕ, maxGap n k ~ f n := by
  sorry

end Erdos693
