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
# Erdős Problem 1023

Maximal antichain families.

SOLVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1023](https://www.erdosproblems.com/1023)
-/

open Finset

open scoped Topology Real

namespace Erdos1023

/--
English version:  Maximum size of antichain family -/
noncomputable def F (n : ℕ) : ℕ := sorry

/--
English version:  -/
@[category research solved, AMS 05]
theorem antichain_family_asymptotic :
    ∃ (c : ℝ), 0 < c ∧
      Filter.Tendsto (fun n => (F n : ℝ) / (c * 2 ^ n / Real.sqrt n))
        Filter.atTop (nhds 1) := by
  sorry

end Erdos1023
