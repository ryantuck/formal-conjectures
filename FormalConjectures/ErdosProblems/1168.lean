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
# Erdős Problem 1168

Partition relations for uncountable cardinals.

OPEN

*Reference:* [erdosproblems.com/1168](https://www.erdosproblems.com/1168)
-/

open Finset Filter Cardinal Ordinal

open scoped Topology Real

namespace Erdos1168

/-- Negation of partition relation: there exists a coloring with no monochromatic set
    of the required size. -/
def PartitionRelationFails (α : Type*) (r : ℕ) (gamma : Type*) (targets : gamma → Type*) : Prop :=
  ∃ (coloring : Finset α → gamma),
    ∀ (color : gamma) (H : Set α),
      (∃ (f : targets color → α), Function.Injective f ∧ Set.range f ⊆ H) →
      ∃ (s : Finset α), s.card = r ∧ (↑s : Set α) ⊆ H ∧ coloring s ≠ color

/-- Problem of Erdős, Hajnal, and Rado:

    Prove that the partition relation fails for a type of cardinality ℵ_{ω+1}
    with 2-element subsets, countably many colors (each appearing at most 3 times),
    and target size ℵ_{ω+1}, without assuming GCH.

    This states that ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, …, 3)_{ℵ_0}^2 independently of GCH. -/
@[category research open, AMS 03]
theorem partition_relation_fails_aleph_omega_plus_one :
    ∀ (α : Type*) [Infinite α],
    ∀ (gamma : Type*) [Countable gamma],
      PartitionRelationFails α 2 gamma (fun _ => Fin 3 ⊕ α) := by
  sorry

end Erdos1168
