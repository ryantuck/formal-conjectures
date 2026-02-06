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
# Erdős Problem 796

Largest g₃(n) with <3 product representations.

OPEN

*Reference:* [erdosproblems.com/796](https://www.erdosproblems.com/796)
-/

open Finset

open scoped Topology Real

namespace Erdos796

/-- g₃(n): largest subset with <3 product representations -/
noncomputable def g3 (n : ℕ) : ℕ := sorry

/-- Conjecture for g₃(n) -/
@[category research open, AMS 11]
theorem product_representations_bound (answer : Prop) :
    answer ↔ ∃ c : ℝ, Filter.Tendsto
      (fun n => (g3 n : ℝ) / ((Real.log (Real.log n) / Real.log n) * n +
        (c + sorry) * n / Real.log n))
      Filter.atTop (nhds 1) := by
  sorry

end Erdos796
