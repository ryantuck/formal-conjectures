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
# Erdős Problem 608

For a graph with n vertices and > n²/4 edges, must at least (2/9)n² edges be contained
in a C₅ (5-cycle)?

DISPROVED by Füredi and Maleki

*Reference:* [erdosproblems.com/608](https://www.erdosproblems.com/608)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos608

variable {α : Type*} [Fintype α]

/-- Negation: there exist graphs with > n²/4 edges but < (2/9)n² edges in C₅ -/
@[category research solved, AMS 05]
theorem not_two_ninths_edges_in_c5 :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.edgeSet.ncard > n^2 / 4 →
      sorry ≥ 2 * n^2 / 9 := by
  sorry

end Erdos608
