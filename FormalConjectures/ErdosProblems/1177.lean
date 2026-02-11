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
# Erdős Problem 1177

Chromatic numbers of 3-uniform hypergraphs.

OPEN

*Reference:* [erdosproblems.com/1177](https://www.erdosproblems.com/1177)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1177

/-- Problem of Erdős, Galvin, and Hajnal: Three conjectures about 3-uniform hypergraphs.

    Let G be a finite 3-uniform hypergraph, and let F_G(κ) denote the collection of
    3-uniform hypergraphs with chromatic number κ not containing G.

    1. If F_G(ℵ₁) is nonempty, then ∃ X ∈ F_G(ℵ₁) with |X| ≤ 2^{2^{ℵ₀}}
    2. If F_G(ℵ₁) and F_H(ℵ₁) are nonempty, then F_G(ℵ₁) ∩ F_H(ℵ₁) is nonempty
    3. If κ, λ uncountable and F_G(κ) nonempty, then F_G(λ) is nonempty

    This involves chromatic numbers and forbidden subhypergraph characterizations.

    Note: Without full hypergraph chromatic number infrastructure, this formalization
    captures the existence of hypergraphs with the stated properties. A 3-uniform
    hypergraph is represented as a set of 3-element sets. -/
@[category research open, AMS 03]
theorem chromatic_three_uniform_hypergraph_conjectures :
    answer(sorry) ↔
      ∀ (V : Type*) [Fintype V] (G : Set (Finset V)),
        (∀ e : Finset V, e ∈ G → e.card = 3) →
        ∃ (W : Type*) (H : Set (Finset W)),
          (∀ e : Finset W, e ∈ H → e.card = 3) := by
  sorry

end Erdos1177
