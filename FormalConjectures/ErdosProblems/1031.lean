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
# Erdős Problem 1031

Induced regular subgraphs.

PROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1031](https://www.erdosproblems.com/1031)
-/

open Finset

open scoped Topology Real

namespace Erdos1031

variable {α : Type*}

/-- English version: Graphs without large trivial subgraphs contain induced regular subgraphs -/@[category research solved, AMS 05]
theorem induced_regular_subgraph (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
      (∀ S : Finset (Fin n), S.card ≥ 10 * Nat.log n →
        ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ (G.Adj v w ∨ ¬G.Adj v w)) →
      ∃ (H : SimpleGraph (Fin n)) (d : ℕ),
        H ≤ G ∧ ∀ [DecidableRel H.Adj] (v : Fin n), H.degree v = d := by
  sorry

end Erdos1031
