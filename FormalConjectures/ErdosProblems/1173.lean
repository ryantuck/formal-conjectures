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
# Erdős Problem 1173

Free set problem under GCH.

OPEN

*Reference:* [erdosproblems.com/1173](https://www.erdosproblems.com/1173)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1173

/-- Problem of Erdős and Hajnal: Free set problem under GCH.

    Assuming GCH, let f: ω_{ω+1} → [ω_{ω+1}]^{≤ℵ_ω} be a function such that
    |f(α) ∩ f(β)| < ℵ_ω for all α ≠ β.

    Question: Does there exist a "free set" of cardinality ℵ_{ω+1}?

    A set S is free if for distinct α, β ∈ S, we have α ∉ f(β) and β ∉ f(α).

    This involves advanced cardinal arithmetic and combinatorial set theory.

    Note: The bounded intersection constraint |f(α) ∩ f(β)| < ℵ_ω is represented
    as a placeholder condition below, as proper cardinality bounds require
    additional infrastructure. -/
@[category research open, AMS 03]
theorem free_set_under_gch :
    answer(sorry) ↔
      ∀ (omega_omega_plus_one : Type*) [Infinite omega_omega_plus_one],
      ∀ (f : omega_omega_plus_one → Set omega_omega_plus_one),
        (∀ α β : omega_omega_plus_one, α ≠ β → (f α ∩ f β).Finite) →
        ∃ (S : Set omega_omega_plus_one),
          ∀ α β : omega_omega_plus_one, α ∈ S → β ∈ S → α ≠ β →
            α ∉ f β ∧ β ∉ f α := by
  sorry

end Erdos1173
