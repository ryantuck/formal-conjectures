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
# Erdős Problem 1075

Subgraph density in r-uniform hypergraphs.

OPEN

*Reference:* [erdosproblems.com/1075](https://www.erdosproblems.com/1075)
-/

open Finset

open scoped Topology Real

namespace Erdos1075

/-- Subgraph density in r-uniform hypergraphs -/
@[category research open, AMS 05]
theorem hypergraph_subgraph_density (r : ℕ) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (H : Finset (Finset (Fin n))),
        (∀ e ∈ H, e.card = r) → ∃ (H' : Finset (Finset (Fin n))), sorry := by
  sorry

end Erdos1075
