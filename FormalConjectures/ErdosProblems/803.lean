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
# Erdős Problem 803

D-balanced subgraph existence.

DISPROVED

*Reference:* [erdosproblems.com/803](https://www.erdosproblems.com/803)
-/

open Finset

open scoped Topology Real

namespace Erdos803

variable {α : Type*}

/-- D-balanced subgraph -/
def isDBalanced (G : SimpleGraph α) (D : ℕ) : Prop := sorry

/-- Disproved: graph with ≥n log n edges has D-balanced subgraph -/
@[category research solved, AMS 05]
theorem not_d_balanced_subgraph :
    ¬ ∃ D : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card ≥ n * Nat.floor (Real.log n) →
      ∃ (S : Set (Fin n)), ∃ (H : SimpleGraph S),
        isDBalanced H D := by
  sorry

end Erdos803
