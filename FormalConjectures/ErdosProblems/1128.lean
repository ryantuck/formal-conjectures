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
# Erdős Problem 1128

Ramsey-type property on cardinality ℵ₁.

DISPROVED

*Reference:* [erdosproblems.com/1128](https://www.erdosproblems.com/1128)
-/

open Finset

open scoped Topology Real

namespace Erdos1128

/-- Let A, B, C be three sets of cardinality aleph_1. In any 2-coloring of A x B x C,
    must there exist A_1 ⊆ A, B_1 ⊆ B, C_1 ⊆ C, all of cardinality aleph_0,
    such that A_1 x B_1 x C_1 is monochromatic?
    Disproved by Prikry and Mills (1978). -/
@[category research solved, AMS 03]
theorem ramsey_aleph_one :
    answer(False) ↔
      (∀ (α β γ : Type*) (_ : Cardinal.mk α = Cardinal.aleph 1)
        (_ : Cardinal.mk β = Cardinal.aleph 1) (_ : Cardinal.mk γ = Cardinal.aleph 1)
        (c : α × β × γ → Fin 2),
        ∃ (A₁ : Set α) (B₁ : Set β) (C₁ : Set γ),
          Cardinal.mk A₁ = Cardinal.aleph 0 ∧
          Cardinal.mk B₁ = Cardinal.aleph 0 ∧
          Cardinal.mk C₁ = Cardinal.aleph 0 ∧
          ∃ color : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ c' ∈ C₁,
            c (a, b, c') = color) := by
  sorry

end Erdos1128
