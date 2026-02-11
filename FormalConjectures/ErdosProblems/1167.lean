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
# Erdős Problem 1167

Cardinal arithmetic and Ramsey theory.

OPEN

*Reference:* [erdosproblems.com/1167](https://www.erdosproblems.com/1167)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1167

/-- A partition relation for types: given a type α, natural number r, type γ of colors,
    and family of target types indexed by γ, the relation holds if every r-coloring
    admits a monochromatic subset of the appropriate size. -/
def PartitionRelation (α : Type*) (r : ℕ) (γ : Type*) (targets : γ → Type*) : Prop :=
  ∀ (coloring : Finset α → γ),
    ∃ (color : γ) (H : Set α),
      (∃ (f : targets color → α), Function.Injective f ∧ Set.range f ⊆ H) ∧
      ∀ (s : Finset α), s.card = r → (↑s : Set α) ⊆ H → coloring s = color

/-- Problem of Erdős, Hajnal, and Rado:

    Let r ≥ 2 be finite, let kappa be an infinite type, and let (kappa_α) be types indexed by γ.
    Does the partition relation for (Set kappa) with r+1 and targets (kappa_α + 1)
    imply the partition relation for kappa with r and targets kappa_α?

    This captures the implication structure between partition relations on cardinals. -/
@[category research open, AMS 03]
theorem partition_relation_implication :
    ∀ (r : ℕ), r ≥ 2 →
    ∀ (kappa : Type*) [Infinite kappa] (gamma : Type*) (kappa_targets : gamma → Type*),
      PartitionRelation (Set kappa) (r + 1) gamma (fun α => Sum (kappa_targets α) Unit) →
      PartitionRelation kappa r gamma kappa_targets := by
  sorry

end Erdos1167
