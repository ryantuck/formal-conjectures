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
# Erdős Problem 1005

Farey sequence ordering problem.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1005](https://www.erdosproblems.com/1005)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1005

/--
English version:  Farey sequence of order n -/
noncomputable def farey (n : ℕ) : List (ℚ) := sorry

/--
English version:  -/
@[category research open, AMS 11]
theorem farey_ordering_linear : answer(sorry) ↔ ∃ (c : ℝ), 0 < c ∧
      Tendsto (fun n => (f n : ℝ) / (c * n)) atTop (nhds 1) := by
  sorry

end Erdos1005
