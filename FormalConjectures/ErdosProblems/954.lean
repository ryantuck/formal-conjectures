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
# Erdős Problem 954

Sequence growth and subset sums.

OPEN

*Reference:* [erdosproblems.com/954](https://www.erdosproblems.com/954)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos954

/-- Special sequence defined by subset sum constraint -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => sorry  -- smallest m with fewer than m solutions to a_i + a_j ≤ m

/-- Growth rate of solutions to a_i + a_j ≤ x -/
@[category research open, AMS 11]
theorem sequence_sum_growth (answer : Prop) :
    answer ↔ ∃ (c : ℝ), 0 < c ∧
      Tendsto (fun x => |{(i, j) : ℕ × ℕ | a i + a j ≤ x}.ncard - x| / x ^ (1/4 + c : ℝ))
        atTop (nhds 0) := by
  sorry

end Erdos954
