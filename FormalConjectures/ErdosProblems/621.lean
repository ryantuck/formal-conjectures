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
# Erdős Problem 621

For a graph G on n vertices, is α₁(G) + τ₁(G) ≤ n²/4, where α₁(G) is the max number
of edges with at most one edge per triangle, and τ₁(G) is the min number of edges
hitting every triangle?

PROVED by Norin and Sun

*Reference:* [erdosproblems.com/621](https://www.erdosproblems.com/621)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos621

variable {α : Type*} [Fintype α]

/-- α₁(G): max edges with ≤ 1 edge per triangle -/
noncomputable def α₁ {β : Type*} (G : SimpleGraph β) : ℕ := sorry

/-- τ₁(G): min edges hitting every triangle -/
noncomputable def τ₁ {β : Type*} (G : SimpleGraph β) : ℕ := sorry

/-- α₁(G) + τ₁(G) ≤ n²/4 -/
@[category research solved, AMS 05]
theorem edge_packing_covering_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    α₁ G + τ₁ G ≤ n^2 / 4 := by
  sorry

end Erdos621
