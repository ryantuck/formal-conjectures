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
# Erdős Problem 750

Infinite chromatic with large independent sets.

OPEN

*Reference:* [erdosproblems.com/750](https://www.erdosproblems.com/750)
-/

open Finset

open scoped Topology Real

namespace Erdos750

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ∞ := sorry

/-- Independence number -/
noncomputable def independenceNumber (G : SimpleGraph α) : ℕ := sorry

/-- Infinite chromatic with large independent sets -/
@[category research open, AMS 05]
theorem infinite_chromatic_large_independent (answer : Prop) :
    answer ↔ ∀ (f : ℕ → ℝ), Filter.Tendsto f Filter.atTop Filter.atTop →
      ∃ (G : SimpleGraph α),
        chromaticNumber G = ⊤ ∧
        ∀ (S : Finset α),
          independenceNumber (G.induce S) ≥ S.card / 2 - f S.card := by
  sorry

end Erdos750
