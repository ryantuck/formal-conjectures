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
# Erdős Problem 1015

Monochromatic partition of edges.

SOLVED

*Reference:* [erdosproblems.com/1015](https://www.erdosproblems.com/1015)
-/

open Finset

open scoped Topology Real

namespace Erdos1015

variable {α : Type*}

/-- Partition edges into vertex-disjoint monochromatic cliques -/
@[category research solved, AMS 05]
theorem monochromatic_edge_partition (n t : ℕ) :
    ∀ (c : α × α → Fin 2),
      ∃ (cliques : Finset (Finset α)),
        (∀ C ∈ cliques, C.card = t ∧ sorry) ∧
        (∀ C₁ ∈ cliques, ∀ C₂ ∈ cliques, C₁ ≠ C₂ → Disjoint C₁ C₂) := by
  sorry

end Erdos1015
