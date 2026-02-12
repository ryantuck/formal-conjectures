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
# Erdős Problem 1019

Saturated planar subgraphs.

PROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1019](https://www.erdosproblems.com/1019)
-/

open Finset

open scoped Topology Real

namespace Erdos1019

variable {α : Type*}

/--
English version:  Graph is planar -/
def IsPlanar (G : SimpleGraph α) : Prop := sorry

/--
English version:  -/
@[category research solved, AMS 05]
theorem saturated_planar_subgraph (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      Nat.floor ((n : ℝ) ^ 2 / 4) + Nat.floor (((n : ℝ) + 1) / 2) ≤ G.edgeFinset.card →
      ∃ (H : SimpleGraph (Fin n)),
        H ≤ G ∧ IsPlanar H ∧
        (∀ u v : Fin n, ¬H.Adj u v → (∃ K : SimpleGraph (Fin n), K ≤ G ∧ ¬IsPlanar K)) := by
  sorry

end Erdos1019
