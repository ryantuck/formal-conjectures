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
# Erdős Problem 775

Hypergraph clique sizes.

DISPROVED

*Reference:* [erdosproblems.com/775](https://www.erdosproblems.com/775)
-/

open Finset

open scoped Topology Real

namespace Erdos775

/-- Number of distinct clique sizes -/
noncomputable def numDistinctCliqueSizes (H : Finset (Finset ℕ)) : ℕ := sorry

/-- Disproved: 3-uniform hypergraph has n-O(1) clique sizes -/
@[category research solved, AMS 05]
theorem not_hypergraph_many_clique_sizes :
    ¬ ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, e.card = 3) →
      numDistinctCliqueSizes H ≥ n - sorry := by
  sorry

end Erdos775
