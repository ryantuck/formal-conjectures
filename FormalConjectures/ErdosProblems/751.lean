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
# Erdős Problem 751

Chromatic 4 graphs have close cycle lengths.

DISPROVED (LEAN verified)

*Reference:* [erdosproblems.com/751](https://www.erdosproblems.com/751)
-/

open Finset

open scoped Topology Real

namespace Erdos751

variable {α : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- Cycle lengths in G -/
noncomputable def cycleLengths (G : SimpleGraph α) : Set ℕ := sorry

/-- Graphs with chromatic 4 have cycles differing by at most 2 -/
@[category research solved, AMS 05]
theorem chromatic_four_close_cycles :
    ∀ (G : SimpleGraph α),
      chromaticNumber G = 4 →
      ∃ m₁ m₂ : ℕ, m₁ ∈ cycleLengths G ∧ m₂ ∈ cycleLengths G ∧
        m₂ - m₁ ≤ 2 := by
  sorry

end Erdos751
