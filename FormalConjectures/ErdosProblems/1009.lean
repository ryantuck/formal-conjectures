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
# Erdős Problem 1009

Edge-disjoint triangles in dense graphs.

PROVED

*Reference:* [erdosproblems.com/1009](https://www.erdosproblems.com/1009)
-/

open Finset

open scoped Topology Real

namespace Erdos1009

variable {α : Type*}

/-- Dense graphs contain many edge-disjoint triangles -/
@[category research solved, AMS 05]
theorem edge_disjoint_triangles (c : ℝ) (hc : 0 < c) :
    ∃ (f : ℝ → ℕ),
      ∀ (n k : ℕ), k < c * n →
        ∀ (G : SimpleGraph (Fin n)),
          Nat.floor (n ^ 2 / 4) + k ≤ G.edgeFinset.card →
          ∃ (triangles : Finset (Finset (Fin n))),
            k - f c ≤ triangles.card ∧
            (∀ T ∈ triangles, T.card = 3 ∧ G.IsClique T) ∧
            (∀ T₁ ∈ triangles, ∀ T₂ ∈ triangles, T₁ ≠ T₂ →
              ∀ e ∈ T₁.product T₁, e ∉ T₂.product T₂) := by
  sorry

end Erdos1009
