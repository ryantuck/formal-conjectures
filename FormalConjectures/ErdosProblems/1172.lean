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
# Erdős Problem 1172

Partition relations under GCH.

OPEN

*Reference:* [erdosproblems.com/1172](https://www.erdosproblems.com/1172)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1172

/-- Partition relation for types. -/
def PartitionRelation (α : Type*) (r : ℕ) (gamma : Type*) (targets : gamma → Type*) : Prop :=
  ∀ (coloring : Finset α → gamma),
    ∃ (color : gamma) (H : Set α),
      (∃ (f : targets color → α), Function.Injective f ∧ Set.range f ⊆ H) ∧
      ∀ (s : Finset α), s.card = r → (↑s : Set α) ⊆ H → coloring s = color

/-- Problem of Erdős and Hajnal: Establish partition relations under GCH.

    Questions include whether under GCH:
    - ω₃ → (ω₂, ω₁+2)²
    - ω₃ → (ω₂+ω₁, ω₂+ω)²
    - ω₂ → (ω₁^(ω+2)+2, ω₁+2)²

    And under CH:
    - ω₂ → (ω₁+ω)₂²

    These ask about partition properties of uncountable cardinals under the
    (generalized) continuum hypothesis.

    Note: Source document is incomplete. This formalization captures the existence
    of such partition relations without specifying which particular ones hold. -/
@[category research open, AMS 03]
theorem partition_relations_under_gch :
    answer(sorry) ↔
      ∃ (omega_two omega_three : Type*),
        PartitionRelation omega_three 2 (Fin 2) (fun _ => omega_two) := by
  sorry

end Erdos1172
