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
# Erdős Problem 613

For a graph G on n ≥ 3 vertices with C(2n+1,2) - C(n,2) - 1 edges, must G decompose
into a bipartite graph and a graph with maximum degree < n?

DISPROVED

*Reference:* [erdosproblems.com/613](https://www.erdosproblems.com/613)
-/

open SimpleGraph Nat

open scoped Topology Real

namespace Erdos613

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A graph is bipartite -/
def IsBipartite (G : SimpleGraph α) : Prop :=
  ∃ (A B : Set α), (∀ a ∈ A, ∀ b ∈ B, a ≠ b) ∧
    (∀ v w, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A))

/-- Negation: graph with specified edge count doesn't decompose as required -/
@[category research solved, AMS 05]
theorem not_bipartite_decomposition :
    ¬ ∀ (n : ℕ) (hn : n ≥ 3) (G : SimpleGraph (Fin n)),
      G.edgeSet.ncard = Nat.choose (2*n+1) 2 - Nat.choose n 2 - 1 →
      ∃ (B D : SimpleGraph (Fin n)),
        IsBipartite B ∧
        (∀ v [DecidableRel D.Adj], D.degree v < n) ∧
        sorry := by
  sorry

end Erdos613
