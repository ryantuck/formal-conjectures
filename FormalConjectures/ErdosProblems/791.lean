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
# Erdős Problem 791

Minimal g(n) for sumset covering.

OPEN (conjecture g(n) ~ 2n^(1/2))

*Reference:* [erdosproblems.com/791](https://www.erdosproblems.com/791)
-/

open Finset

open scoped Topology Real

namespace Erdos791

/-- g(n): minimal size such that {0,...,n} ⊆ A+A -/
noncomputable def g (n : ℕ) : ℕ := sorry

/-- Conjecture: g(n) ~ 2n^(1/2) -/
@[category research open, AMS 11]
theorem sumset_covering_asymptotic (answer : Prop) :
    answer ↔ Filter.Tendsto
      (fun n => (g n : ℝ) / (2 * (n : ℝ) ^ (1/2 : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

end Erdos791
