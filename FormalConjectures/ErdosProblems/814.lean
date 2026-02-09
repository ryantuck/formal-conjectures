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
# Erdős Problem 814

Induced subgraph with large minimum degree.

PROVED

*Reference:* [erdosproblems.com/814](https://www.erdosproblems.com/814)
-/

open Finset

open scoped Topology Real

namespace Erdos814

/-- Graph with enough edges has induced subgraph with min degree k -/
@[category research solved, AMS 05]
theorem induced_large_min_degree (k : ℕ) :
    ∃ c : ℝ, c > 0 ∧ c < 1 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [G.LocallyFinite],
        G.edgeFinset.card ≥ k * n →
        ∃ (S : Finset (Fin n)) (_ : (G.induce ↑S).LocallyFinite),
          (S.card : ℝ) ≤ (1 - c) * n ∧
          ∀ v : S, (G.induce ↑S).degree v ≥ k := by
  sorry

end Erdos814
