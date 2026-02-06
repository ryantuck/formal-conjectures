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
# Erdős Problem 1014

Ramsey number limit ratio.

OPEN

*Reference:* [erdosproblems.com/1014](https://www.erdosproblems.com/1014)
-/

open Finset

open scoped Topology Real

namespace Erdos1014

/-- Ramsey number R(k,l) -/
noncomputable def R (k l : ℕ) : ℕ := sorry

/-- Ramsey number ratio approaches 1 -/
@[category research open, AMS 05]
theorem ramsey_ratio_limit (k : ℕ) (hk : 3 ≤ k) (answer : Prop) :
    answer ↔ Filter.Tendsto (fun l => (R k (l + 1) : ℝ) / R k l)
      Filter.atTop (nhds 1) := by
  sorry

end Erdos1014
