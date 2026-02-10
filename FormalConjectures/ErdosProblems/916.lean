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
# Erdős Problem 916

Graph cycles and adjacent vertices.

PROVED

*Reference:* [erdosproblems.com/916](https://www.erdosproblems.com/916)
-/

open Finset

open scoped Topology Real

namespace Erdos916

variable {α : Type*}

/-- A cycle in a graph (simplified formulation) -/
def IsCycle (G : SimpleGraph α) (C : List α) : Prop :=
  C.length ≥ 3 ∧ C.Nodup ∧
  (∀ i (hi : i < C.length), G.Adj (C.get ⟨i, hi⟩) (C.get ⟨(i + 1) % C.length, Nat.mod_lt _ (Nat.zero_lt_of_lt hi)⟩))

/-- Graph cycles and adjacent vertices property -/
@[category research solved, AMS 05]
theorem cycles_adjacent_vertices (k : ℕ) (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, k ≤ G.degree v) →
      ∃ (C : List (Fin n)),
        IsCycle G C ∧
        ∀ v ∈ C, ∃ u : Fin n, u ∉ C ∧ G.Adj v u := by
  sorry

end Erdos916
