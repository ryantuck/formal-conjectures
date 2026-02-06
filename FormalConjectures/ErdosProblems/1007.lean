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
# Erdős Problem 1007

Dimension of a graph with minimum edges.

SOLVED

*Reference:* [erdosproblems.com/1007](https://www.erdosproblems.com/1007)
-/

open Finset

open scoped Topology Real

namespace Erdos1007

variable {α : Type*}

/-- Graph dimension -/
noncomputable def dimension (G : SimpleGraph α) : ℕ := sorry

/-- Minimum edges for dimension 4 is 9 -/
@[category research solved, AMS 05]
theorem min_edges_dimension_four :
    (∀ (G : SimpleGraph α) [Fintype α],
      dimension G = 4 →
      9 ≤ G.edgeFinset.card) ∧
    (∃ (G : SimpleGraph (Fin sorry)) [Fintype (Fin sorry)],
      dimension G = 4 ∧ G.edgeFinset.card = 9) := by
  sorry

end Erdos1007
