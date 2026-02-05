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
# Erdős Problem 583

Can every connected graph on n vertices be partitioned into at most ⌈n/2⌉ edge-disjoint paths?

OPEN

*Reference:* [erdosproblems.com/583](https://www.erdosproblems.com/583)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos583

variable {α : Type*} [Fintype α]

/-- Every connected graph partitions into ⌈n/2⌉ edge-disjoint paths -/
@[category research open, AMS 05]
theorem connected_graph_path_partition (G : SimpleGraph α) (hconn : G.Connected) :
    ∃ (paths : Finset (Finset (α × α))),
      paths.card ≤ (Fintype.card α + 1) / 2 ∧
      (∀ P ∈ paths, ∀ (e : α × α), e ∈ P → G.Adj e.1 e.2) ∧
      (∀ P₁ P₂, P₁ ∈ paths → P₂ ∈ paths → P₁ ≠ P₂ → Disjoint P₁ P₂) ∧
      (∀ v w, G.Adj v w → ∃ P ∈ paths, (v, w) ∈ P ∨ (w, v) ∈ P) := by
  sorry

end Erdos583
