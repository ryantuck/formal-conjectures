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
# Erdős Problem 1012

Cycle existence with edge density constraints.

SOLVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1012](https://www.erdosproblems.com/1012)
-/

open Finset

open scoped Topology Real

namespace Erdos1012

variable {α : Type*}

/-- A cycle in a graph (simplified formulation) -/
def IsCycle (G : SimpleGraph α) (C : List α) : Prop :=
  C.length ≥ 3 ∧ C.Nodup ∧
  (∀ i (hi : i < C.length), G.Adj (C.get ⟨i, hi⟩) (C.get ⟨(i + 1) % C.length, Nat.mod_lt _ (Nat.zero_lt_of_lt hi)⟩))

/--
English version:  Minimum n for cycle existence threshold -/
noncomputable def f (k : ℕ) : ℕ := sorry

/--
English version:  -/
@[category research solved, AMS 05]
theorem cycle_edge_density (k n : ℕ) :
    f k ≤ n →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + 1 ≤ G.edgeFinset.card →
      ∃ (C : List (Fin n)),
        IsCycle G C ∧ C.length = n - k := by
  sorry

end Erdos1012
