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
# Erdős Problem 793

Maximum F(n) avoiding divisibility relation.

OPEN

*Reference:* [erdosproblems.com/793](https://www.erdosproblems.com/793)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos793

/-- F(n): maximum subset avoiding at = b with smallest prime factor > a -/
noncomputable def F (N : ℕ) : ℕ := sorry

/-- Conjecture for F(n) -/
@[category research open, AMS 11]
theorem divisibility_avoidance_bound (answer : Prop) :
    answer ↔ ∃ C : ℝ, ∀ᶠ (N : ℕ) in Filter.atTop,
      F N = (Finset.filter Nat.Prime (Finset.range (N + 1))).card +
        (C + sorry) * (N : ℝ) ^ (2/3 : ℝ) * (Real.log N) ^ (-2) := by
  sorry

end Erdos793
