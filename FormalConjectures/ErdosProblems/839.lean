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
# Erdős Problem 839

Sequence avoiding consecutive sums.

OPEN

*Reference:* [erdosproblems.com/839](https://www.erdosproblems.com/839)
-/

open Finset

open scoped Topology Real BigOperators

namespace Erdos839

/-- Sequence with no consecutive sum property -/
def NoConsecutiveSum (a : ℕ → ℕ) : Prop := sorry

/-- Does limsup(aₙ/n) = ∞? -/
@[category research open, AMS 11]
theorem consecutive_sum_growth_one (answer : Prop) :
    answer ↔ ∀ (a : ℕ → ℕ),
      StrictMono a →
      a 0 = 1 →
      NoConsecutiveSum a →
      Filter.limsup (fun n => (a n : ℝ) / n) Filter.atTop = ⊤ := by
  sorry

/-- Does lim (1/log x) Σ(1/aₙ) = 0? -/
@[category research open, AMS 11]
theorem consecutive_sum_reciprocal (answer : Prop) :
    answer ↔ sorry := by
  sorry

end Erdos839
