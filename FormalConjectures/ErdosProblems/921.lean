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
# Erdős Problem 921

Chromatic number and odd cycle length.

PROVED

*Reference:* [erdosproblems.com/921](https://www.erdosproblems.com/921)
-/

open Finset

open scoped Topology Real

namespace Erdos921

variable {α : Type*}

/-- A cycle in a graph (simplified formulation) -/
def IsCycle (G : SimpleGraph α) (C : List α) : Prop :=
  C.length ≥ 3 ∧ C.Nodup ∧
  (∀ i (hi : i < C.length), G.Adj (C.get ⟨i, hi⟩) (C.get ⟨(i + 1) % C.length, Nat.mod_lt _ (Nat.zero_lt_of_lt hi)⟩))

/-- Graphs with large chromatic number contain long odd cycles -/
@[category research solved, AMS 05]
theorem chromatic_odd_cycle (k : ℕ) :
    ∀ (G : SimpleGraph α) [Fintype α],
      k ≤ G.chromaticNumber →
      ∃ (C : List α), IsCycle G C ∧ Odd C.length ∧ k ≤ C.length := by
  sorry

end Erdos921
