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
# Erdős Problem 767

Cycle with k chords edge bound.

PROVED

*Reference:* [erdosproblems.com/767](https://www.erdosproblems.com/767)
-/

open Finset

open scoped Topology Real

namespace Erdos767

/-- Maximum edges avoiding cycle with k chords from vertex -/
@[category research solved, AMS 05]
theorem cycle_k_chords_edge_bound (n k : ℕ) (hn : n ≥ 3 * k + 3) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ C : sorry, sorry) →
      G.edgeFinset.card ≤ (k + 1) * n - (k + 1) ^ 2 := by
  sorry

end Erdos767
