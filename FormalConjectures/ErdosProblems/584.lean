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
# Erdős Problem 584

Let G be a graph with n vertices and δn² edges. Determine whether G must contain:
(a) a subgraph H₁ with ≫ δ³n² edges where every two edges lie on a cycle of length ≤ 6
(b) a subgraph H₂ with ≫ δ²n² edges where every two edges lie on a cycle of length ≤ 8

OPEN

*Reference:* [erdosproblems.com/584](https://www.erdosproblems.com/584)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos584

variable {α : Type*} [Fintype α]

/-- Dense graph contains subgraph where edge pairs lie on short cycles (part a) -/
@[category research open, AMS 05]
theorem dense_graph_short_cycles_part_a (δ : ℝ) (hδ : δ > 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (G : SimpleGraph (Fin n)),
      G.edgeSet.ncard ≥ Nat.floor (δ * n^2) →
      ∃ (H : SimpleGraph (Fin n)),
        (∀ v w, H.Adj v w → G.Adj v w) ∧
        H.edgeSet.ncard ≥ Nat.floor (c * δ^3 * n^2) ∧
        (∀ e₁ e₂ : Fin n × Fin n, H.Adj e₁.1 e₁.2 → H.Adj e₂.1 e₂.2 →
          ∃ (w : H.Walk e₁.1 e₁.1), w.length ≤ 6 ∧ sorry) := by
  sorry

/-- Dense graph contains subgraph where edge pairs lie on cycles ≤ 8 (part b) -/
@[category research open, AMS 05]
theorem dense_graph_short_cycles_part_b (δ : ℝ) (hδ : δ > 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (G : SimpleGraph (Fin n)),
      G.edgeSet.ncard ≥ Nat.floor (δ * n^2) →
      ∃ (H : SimpleGraph (Fin n)),
        (∀ v w, H.Adj v w → G.Adj v w) ∧
        H.edgeSet.ncard ≥ Nat.floor (c * δ^2 * n^2) ∧
        (∀ e₁ e₂ : Fin n × Fin n, H.Adj e₁.1 e₁.2 → H.Adj e₂.1 e₂.2 →
          ∃ (w : H.Walk e₁.1 e₁.1), w.length ≤ 8) := by
  sorry

end Erdos584
