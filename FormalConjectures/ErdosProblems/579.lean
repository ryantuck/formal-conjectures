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
# Erdős Problem 579

Let δ > 0. If n is sufficiently large and G is a graph on n vertices with no K_{2,2,2}
and at least δn² edges, then G contains an independent set of size ≫ n.

OPEN (proved for δ > 1/8)

*Reference:* [erdosproblems.com/579](https://www.erdosproblems.com/579)
-/

open SimpleGraph Finset

open scoped Topology Real

namespace Erdos579

variable {α : Type*} [Fintype α]

/-- The complete tripartite graph K_{2,2,2} (octahedron) -/
def octahedron : SimpleGraph (Fin 6) := sorry

/-- Dense K_{2,2,2}-free graph has large independent set -/
@[category research open, AMS 05]
theorem dense_octahedron_free_independent_set (δ : ℝ) (hδ : δ > 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (G : SimpleGraph (Fin n)),
      (∀ (f : Fin 6 ↪ Fin n), ¬ ∀ i j, octahedron.Adj i j ↔ G.Adj (f i) (f j)) →
      G.edgeSet.ncard ≥ Nat.floor (δ * n^2) →
      ∃ (S : Finset (Fin n)), (∀ i j, i ∈ S → j ∈ S → ¬ G.Adj i j) ∧ S.card ≥ Nat.floor (c * n) := by
  sorry

end Erdos579
