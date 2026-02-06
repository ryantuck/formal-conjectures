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
# Erdős Problem 761

Chromatic vs dichromatic number.

OPEN

*Reference:* [erdosproblems.com/761](https://www.erdosproblems.com/761)
-/

open Finset

open scoped Topology Real

namespace Erdos761

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Dichromatic number -/
noncomputable def dichromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Cochromatic number -/
noncomputable def cochromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Large chromatic implies large dichromatic -/
@[category research open, AMS 05]
theorem chromatic_dichromatic_relation (answer : Prop) :
    answer ↔ ∀ (f : ℕ → ℕ), Filter.Tendsto f Filter.atTop Filter.atTop →
      ∀ (G : SimpleGraph α),
        chromaticNumber G ≥ f (dichromaticNumber G) →
        sorry := by
  sorry

end Erdos761
