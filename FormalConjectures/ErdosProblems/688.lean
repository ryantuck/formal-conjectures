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
# Erdős Problem 688

Estimate εₙ (maximal value for congruence covering). Is εₙ = o(1)?

OPEN

*Reference:* [erdosproblems.com/688](https://www.erdosproblems.com/688)
-/

open Nat

open scoped Topology Real

namespace Erdos688

/-- εₙ: maximal value for congruence covering -/
noncomputable def ε (n : ℕ) : ℝ := sorry

/-- Is εₙ = o(1)? -/
@[category research open, AMS 11]
theorem epsilon_n_tends_to_zero (answer : Prop) :
    answer ↔ Filter.Tendsto ε Filter.atTop (nhds 0) := by
  sorry

end Erdos688
