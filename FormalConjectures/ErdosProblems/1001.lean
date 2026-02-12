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
# Erdős Problem 1001

Limit of Diophantine approximation set measure.

SOLVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1001](https://www.erdosproblems.com/1001)
-/

open Finset Filter MeasureTheory

open scoped Topology Real

namespace Erdos1001

/--
English version:  Measure of Diophantine approximation set -/
noncomputable def S (N : ℕ) (A c : ℝ) : ℝ := sorry

/--
English version:  -/
@[category research solved, AMS 11]
theorem diophantine_set_limit (A c : ℝ) :
    ∃ (f : ℝ → ℝ → ℝ),
      Tendsto (fun N => S N A c) atTop (nhds (f A c)) := by
  sorry

end Erdos1001
