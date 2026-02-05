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
# Erdős Problem 565

*Reference:* [erdosproblems.com/565](https://www.erdosproblems.com/565)

## Statement (PROVED)
The induced Ramsey number R*(G) is the minimum m such that there exists a graph H on m vertices
where any 2-coloring of H's edges contains an induced monochromatic copy of G.

Conjecture (now proved): R*(G) ≤ 2^O(n) for any graph G on n vertices.

Proved by Aragão, Campos, Dahia, Filipe, Marciano in 2025.

## Source
Original conjecture by Erdős, Hajnal, and Pósa
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos565

/-- The induced Ramsey number: smallest m guaranteeing monochromatic induced copies of G
    under any edge 2-coloring of an m-vertex graph -/
def inducedRamseyNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := sorry

/-- Main theorem: R*(G) ≤ 2^O(n) for any graph G on n vertices (PROVED) -/
@[category research solved, AMS 05]
theorem induced_ramsey_exponential (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ c : ℝ, c > 0 ∧ (inducedRamseyNumber G : ℝ) ≤ 2^(c * n) :=
  sorry

end Erdos565
