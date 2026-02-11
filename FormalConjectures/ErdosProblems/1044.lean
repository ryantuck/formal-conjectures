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
# Erdős Problem 1044

Level set boundary length.

SOLVED

*Reference:* [erdosproblems.com/1044](https://www.erdosproblems.com/1044)
-/

open Finset

open scoped Topology Real

namespace Erdos1044

/-- Maximum boundary length of level set components -/
noncomputable def Λ (f : Polynomial ℂ) : ℝ := sorry

/-- Infimum of boundary length is 2 -/
@[category research solved, AMS 30]
theorem level_set_boundary_length :
    sInf {y | ∃ (f : Polynomial ℂ), f.Monic ∧
      (∀ z : ℂ, f.IsRoot z → ‖z‖ ≤ 1) ∧ y = Λ f} = 2 := by
  sorry

end Erdos1044
