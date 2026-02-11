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
# Erdős Problem 1170

Consistency of partition properties for ω₂.

OPEN

*Reference:* [erdosproblems.com/1170](https://www.erdosproblems.com/1170)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1170

/-- Partition relation for types (reusing definition from 1167). -/
def PartitionRelation (α : Type*) (r : ℕ) (gamma : Type*) (targets : gamma → Type*) : Prop :=
  ∀ (coloring : Finset α → gamma),
    ∃ (color : gamma) (H : Set α),
      (∃ (f : targets color → α), Function.Injective f ∧ Set.range f ⊆ H) ∧
      ∀ (s : Finset α), s.card = r → (↑s : Set α) ⊆ H → coloring s = color

/-- Is it consistent (in ZFC) that ω₂ → (α)₂² for every α < ω₂?

    This asks whether there exists a model of set theory where the second uncountable
    cardinal ω₂ has the partition property that every 2-coloring of pairs contains,
    for any ordinal α < ω₂, a monochromatic subset of order type α.

    Laver and Foreman-Hajnal proved related consistency results. -/
@[category research open, AMS 03]
theorem partition_omega_two_consistency :
    answer(sorry) ↔
      ∀ (alpha_type : Type*) (omega_two_type : Type*) [Infinite omega_two_type],
        PartitionRelation omega_two_type 2 (Fin 2) (fun _ => alpha_type) := by
  sorry

end Erdos1170
