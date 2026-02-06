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
# Erdős Problem 904

Triangle with large degree sum.

PROVED

*Reference:* [erdosproblems.com/904](https://www.erdosproblems.com/904)
-/

open Finset

open scoped Topology Real

namespace Erdos904

/-- Graph with >n²/4 edges has triangle with degree sum ≥(3/2)n -/
@[category research solved, AMS 05]
theorem triangle_large_degree_sum (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ (a b c : Fin n),
        G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
        G.degree a + G.degree b + G.degree c ≥ (3 * n) / 2 := by
  sorry

end Erdos904
