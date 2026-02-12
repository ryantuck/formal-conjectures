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
# Erdős Problem 1030

Ramsey number ratio.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1030](https://www.erdosproblems.com/1030)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1030

/--
English version:  Diagonal Ramsey number -/
noncomputable def R (k : ℕ) : ℕ := sorry

/--
English version:  -/
@[category research open, AMS 05]
theorem ramsey_ratio_bound : answer(sorry) ↔ ∃ (c : ℝ), 0 < c ∧
      Filter.Tendsto (fun k => (R (k + 1) : ℝ) / R k) atTop (nhds (1 + c)) ∧
      1 + c > 1 := by
  sorry

end Erdos1030
