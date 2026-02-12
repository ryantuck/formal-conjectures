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
# Erdős Problem 1034

Triangle vertex count.

DISPROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1034](https://www.erdosproblems.com/1034)
-/

open Finset

open scoped Topology Real

namespace Erdos1034

variable {α : Type*}

open Classical in
/-- English version: Dense graphs contain triangles with many adjacent vertices -/@[category research open, AMS 05]
theorem triangle_vertex_count : answer(True) ↔ ∃ (c : ℝ), 0 < c ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (G : SimpleGraph (Fin n)),
        (∀ [DecidableRel G.Adj], G.edgeFinset.card ≥ n^2 / 4 →
          ∃ (u v w : Fin n), G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧
            ({x : Fin n | G.Adj x u ∨ G.Adj x v ∨ G.Adj x w}.toFinset.card : ℝ) ≥ c * (n : ℝ)) := by
  sorry

end Erdos1034
