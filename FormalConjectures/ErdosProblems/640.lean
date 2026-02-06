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
# Erdős Problem 640

Does χ(G) ≥ f(k) imply the odd cycle spanning chromatic number is ≥ k?

OPEN

*Reference:* [erdosproblems.com/640](https://www.erdosproblems.com/640)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos640

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Odd cycle spanning chromatic number -/
noncomputable def oddCycleSpanningChromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- χ(G) ≥ f(k) implies odd cycle spanning chromatic number ≥ k -/
@[category research open, AMS 05]
theorem chromatic_implies_odd_cycle_spanning (k : ℕ) (answer : Prop) :
    answer ↔ ∃ f : ℕ → ℕ, ∀ (G : SimpleGraph α),
      chromaticNumber G ≥ f k →
      oddCycleSpanningChromaticNumber G ≥ k := by
  sorry

end Erdos640
