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
# Erdős Problem 1040

Logarithmic capacity and level sets.

DISPROVED

*Reference:* [erdosproblems.com/1040](https://www.erdosproblems.com/1040)
-/

open Finset

open scoped Topology Real

namespace Erdos1040

/-- Measure of polynomial level set -/
noncomputable def μ (F : Set ℂ) : ℝ := sorry

/-- Transfinite diameter of a set -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ := sorry

/-- Level set measure determined by transfinite diameter -/
@[category research open, AMS 30]
theorem logarithmic_capacity (answer : Prop) :
    answer ↔ ∀ (F : Set ℂ), IsClosed F →
      ∃ (f : ℝ → ℝ), μ F = f (transfiniteDiameter F) := by
  sorry

end Erdos1040
