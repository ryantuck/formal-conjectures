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
# Erdős Problem 719

r-hypergraph union decomposition conjecture.

OPEN

*Reference:* [erdosproblems.com/719](https://www.erdosproblems.com/719)
-/

open Finset

open scoped Topology Real

namespace Erdos719

/-- Turán number for r-uniform complete hypergraph -/
noncomputable def ex_r (n r : ℕ) : ℕ := sorry

/-- Hypergraph union decomposition -/
@[category research open, AMS 05]
theorem hypergraph_union_decomposition (r n : ℕ) (answer : Prop) :
    answer ↔ ∀ (G : Finset (Finset (Fin n))),
      (∀ e ∈ G, e.card = r) →
      sorry := by
  sorry

end Erdos719
