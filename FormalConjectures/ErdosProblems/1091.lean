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
# Erdős Problem 1091

Odd cycles with diagonals in K₄-free graphs.

OPEN

*Reference:* [erdosproblems.com/1091](https://www.erdosproblems.com/1091)
-/

open Finset

open scoped Topology Real

namespace Erdos1091

/-- English version: Let G be a K₄-free graph with chromatic number 4. Must G contain an odd cycle with at least two diagonals? -/
@[category research open, AMS 05]
theorem odd_cycles_with_diagonals :
    answer(sorry) ↔ ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.chromaticNumber = 4 →
      G.CliqueFree 4 →
      ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ Odd w.length ∧
        letI := Classical.propDecidable
        2 ≤ (Finset.univ.filter (λ e : Sym2 V => ¬(e ∈ w.edges) ∧ ∀ u ∈ e, u ∈ w.support ∧ e ∈ G.edgeSet)).card := by
  sorry

end Erdos1091
