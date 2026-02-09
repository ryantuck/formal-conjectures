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
# Erdős Problem 805

Graph with large clique and independence in subgraphs.

OPEN

*Reference:* [erdosproblems.com/805](https://www.erdosproblems.com/805)
-/

open Finset

open scoped Topology Real

namespace Erdos805

variable {α : Type*}

/-- Clique number -/
noncomputable def cliqueNumber (G : SimpleGraph α) : ℕ := sorry

/-- Independence number -/
noncomputable def independenceNumber (G : SimpleGraph α) : ℕ := sorry

/-- For which g(n) does graph exist with property -/
@[category research open, AMS 05]
theorem clique_independence_subgraphs (answer : Prop) :
    answer ↔ ∃ g : ℕ → ℕ, ∀ (n : ℕ),
      ∃ (G : SimpleGraph (Fin n)),
        ∀ (S : Finset (Fin n)),
          S.card = g n →
          cliqueNumber (G.induce S) ≥ Real.log n ∧
          independenceNumber (G.induce S) ≥ Real.log n := by
  sorry

end Erdos805
