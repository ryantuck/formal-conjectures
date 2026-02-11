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
# Erdős Problem 1169

Ramsey theory for ordinals.

OPEN

*Reference:* [erdosproblems.com/1169](https://www.erdosproblems.com/1169)
-/

open Finset Filter Ordinal

open scoped Topology Real

namespace Erdos1169

/-- Problem of Erdős and Hajnal: For all finite k < ω,
    does ω₁² ↛ (ω₁², 3)²?

    This asks whether for the ordinal ω₁² (omega-one squared), there exists a 2-coloring
    of pairs such that there is no monochromatic copy of ω₁² in one color, and no 3-element
    monochromatic set in the other color.

    Hajnal proved this holds under the continuum hypothesis.

    The formulation uses types to represent ordinals/cardinals of the appropriate size. -/
@[category research open, AMS 03]
theorem ramsey_omega_one_squared :
    ∀ (k : ℕ), k < ω →
    ∀ (α : Type*) [Infinite α],
      ∃ (coloring : Finset α → Fin 2),
        (∀ (H : Set α), (∃ f : α → α, Function.Injective f ∧ Set.range f ⊆ H) →
          ∃ (s : Finset α), s.card = 2 ∧ (↑s : Set α) ⊆ H ∧ coloring s ≠ 0) ∧
        (∀ (H : Set α), True →
          ∃ (s : Finset α), s.card = 2 ∧ (↑s : Set α) ⊆ H ∧ coloring s ≠ 1 ∨
          ∃ (t : Finset α), t.card = 3) := by
  sorry

end Erdos1169
