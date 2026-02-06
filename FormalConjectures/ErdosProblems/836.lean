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
# Erdős Problem 836

Chromatic 3 with intersecting edges.

OPEN

*Reference:* [erdosproblems.com/836](https://www.erdosproblems.com/836)
-/

open Finset

open scoped Topology Real

namespace Erdos836

/-- Chromatic number -/
noncomputable def chromaticNumber (H : Finset (Finset α)) : ℕ := sorry

/-- Chromatic 3 with intersecting edges has O(r²) vertices -/
@[category research open, AMS 05]
theorem chromatic_intersecting_vertices (r : ℕ) (answer : Prop) :
    answer ↔ ∃ C : ℝ, C > 0 ∧
      ∀ (H : Finset (Finset (Fin n))),
        (∀ e ∈ H, e.card = r) →
        (∀ e₁ e₂ : Finset (Fin n), e₁ ∈ H → e₂ ∈ H → e₁ ∩ e₂ ≠ ∅) →
        chromaticNumber H = 3 →
        n ≤ C * (r : ℝ) ^ 2 := by
  sorry

end Erdos836
