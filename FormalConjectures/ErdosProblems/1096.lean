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
# Erdős Problem 1096

Gap distribution in q-adic expansions.

OPEN

*Reference:* [erdosproblems.com/1096](https://www.erdosproblems.com/1096)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1096

/-- English version: Let 1 < q < 1 + ε and consider the set of numbers of the shape Σ_{i ∈ S} q^i for all finite S, ordered by size as 0 = x₁ < x₂ < .... Is it true that, provided ε > 0 is sufficiently small, x_{k+1} - x_k → 0? -/
@[category research open, AMS 11]
theorem qadic_gap_distribution :
    answer(sorry) ↔ ∃ ε > 0, ∀ q, 1 < q ∧ q < 1 + ε →
      let X := {x | ∃ (S : Finset ℕ), x = ∑ i ∈ S, q^i}
      ∀ (δ : ℝ), δ > 0 → ∃ (M : ℝ), ∀ x ∈ X, M < x → ∃ y ∈ X, x < y ∧ y - x < δ := by
  sorry

end Erdos1096
