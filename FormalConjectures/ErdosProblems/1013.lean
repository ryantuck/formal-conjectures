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
# Erdős Problem 1013

Asymptotic for triangle-free chromatic graphs.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1013](https://www.erdosproblems.com/1013)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1013

/--
English version:  Minimum n for triangle-free graph with chromatic number k -/
noncomputable def h_3 (k : ℕ) : ℕ := sorry

/--
English version:  -/
@[category research open, AMS 05]
theorem triangle_free_chromatic_asymptotic : answer(sorry) ↔ (∃ (f : ℕ → ℝ),
      Tendsto (fun k => (h_3 k : ℝ) / f k) atTop (nhds 1)) ∧
      Tendsto (fun k => (h_3 (k + 1) : ℝ) / h_3 k) atTop (nhds 1) := by
  sorry

end Erdos1013
