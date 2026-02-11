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
# Erdős Problem 1162

Asymptotic formula for the number of subgroups of S_n.

OPEN

*Reference:* [erdosproblems.com/1162](https://www.erdosproblems.com/1162)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos1162

/-- Let f(n) denote the number of subgroups of the symmetric group S_n.
    Pyber (1993) established that log f(n) ≍ n².
    Roney-Dougal and Tracey (2025) refined this to:  log f(n) = (1/16 + o(1))n²

    This formalization states the refined asymptotic formula. -/
@[category research open, AMS 20]
theorem subgroups_symmetric_group_asymptotic :
    ∃ (f : ℕ → ℕ),
      (fun n => Real.log (f n)) ~[atTop] (fun n => (1/16 : ℝ) * (n : ℝ)^2) := by
  sorry

end Erdos1162
