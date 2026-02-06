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
# Erdős Problem 886

Divisors in narrow interval.

OPEN

*Reference:* [erdosproblems.com/886](https://www.erdosproblems.com/886)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos886

/-- Number of divisors in interval (n^(1/2), n^(1/2) + n^(1/2-ε)) -/
@[category research open, AMS 11]
theorem divisors_narrow_interval (ε : ℝ) (hε : ε > 0) (answer : Prop) :
    answer ↔ ∃ C : ℕ, ∀ (n : ℕ),
      (Finset.filter (fun d => d ∣ n ∧
        (n : ℝ) ^ (1/2 : ℝ) < d ∧
        d ≤ (n : ℝ) ^ (1/2 : ℝ) + (n : ℝ) ^ (1/2 - ε))
        (Finset.range (n + 1))).card ≤ C := by
  sorry

end Erdos886
