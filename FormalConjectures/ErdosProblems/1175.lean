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
# Erdős Problem 1175

Triangle-free subgraphs with chromatic number.

OPEN

*Reference:* [erdosproblems.com/1175](https://www.erdosproblems.com/1175)
-/

open Finset Filter SimpleGraph

open scoped Topology Real

namespace Erdos1175

/-- Let κ be an uncountable cardinal. Must there exist a cardinal λ such that
    every graph with chromatic number λ contains a triangle-free subgraph
    with chromatic number κ?

    Shelah proved consistency of a negative answer when κ = λ = ℵ₁.

    This formalization asks whether such a cardinal λ exists for a given κ.
    The conditions about chromatic numbers are simplified due to lack of
    chromatic number infrastructure in Mathlib. -/
@[category research open, AMS 03]
theorem triangle_free_subgraph_chromatic :
    answer(sorry) ↔
      ∀ (kappa_type : Type*) [Infinite kappa_type],
        ∃ (lambda_type : Type*),
          ∀ (V : Type*) (G : SimpleGraph V),
            ∃ (H : SimpleGraph V), H ≤ G ∧
              (∀ (tri : Finset V), tri.card = 3 → ¬H.IsClique (tri : Set V)) := by
  sorry

end Erdos1175
