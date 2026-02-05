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
# Erdős Problem 622

For regular graph G with 2n vertices and degree n+1, must G contain ≫ 2^{2n} subsets
spanned by a Hamiltonian cycle?

PROVED by Draganic, Keevash, and Müyesser

*Reference:* [erdosproblems.com/622](https://www.erdosproblems.com/622)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos622

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Regular graph with 2n vertices, degree n+1 has ≥ (1/2+o(1))·2^{2n} cycle-spanned subsets -/
@[category research solved, AMS 05]
theorem regular_graph_cycle_spanned_subsets (n : ℕ) (G : SimpleGraph (Fin (2*n)))
    [DecidableRel G.Adj] (hreg : ∀ v, G.degree v = n + 1) :
    ∃ (subsets : Finset (Finset (Fin (2*n)))),
      (∀ S ∈ subsets, ∃ (w : G.Walk sorry sorry), sorry) ∧
      ∀ᶠ (m : ℕ) in Filter.atTop,
        (subsets.card : ℝ) ≥ (1 / 2) * 2 ^ (2 * m) := by
  sorry

end Erdos622
