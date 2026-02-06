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
# Erdős Problem 797

Acyclic chromatic number estimate.

PROVED

*Reference:* [erdosproblems.com/797](https://www.erdosproblems.com/797)
-/

open Finset

open scoped Topology Real

namespace Erdos797

/-- Acyclic chromatic number -/
noncomputable def acyclicChromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- f(d): maximal acyclic chromatic number for degree d -/
noncomputable def f (d : ℕ) : ℕ := sorry

/-- Bounds for f(d) -/
@[category research solved, AMS 05]
theorem acyclic_chromatic_bounds :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ (d : ℕ), c₁ * (d : ℝ) ^ (4/3 : ℝ) / (Real.log d) ^ (1/3 : ℝ) ≤ f d ∧
        f d ≤ c₂ * (d : ℝ) ^ (4/3 : ℝ) := by
  sorry

end Erdos797
