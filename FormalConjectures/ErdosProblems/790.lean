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
# Erdős Problem 790

Estimate l(n) for sum-free subsets.

OPEN

*Reference:* [erdosproblems.com/790](https://www.erdosproblems.com/790)
-/

open Finset

open scoped Topology Real

namespace Erdos790

/-- l(n) for sum-free subsets -/
noncomputable def l (n : ℕ) : ℕ := sorry

/-- Does l(n)/n^(1/2) → ∞? -/
@[category research open, AMS 11]
theorem sum_free_l_growth (answer : Prop) :
    answer ↔ Filter.Tendsto
      (fun n => (l n : ℝ) / (n : ℝ) ^ (1/2 : ℝ))
      Filter.atTop Filter.atTop := by
  sorry

end Erdos790
