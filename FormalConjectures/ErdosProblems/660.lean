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
# Erdős Problem 660

Let x₁,...,xₙ ∈ ℝ³ be vertices of a convex polyhedron.
Are there at least (1-o(1))n/2 distinct distances?

OPEN (Altman proved ≥ n/2)

*Reference:* [erdosproblems.com/660](https://www.erdosproblems.com/660)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos660

/-- Vertices of convex polyhedron have ≥ (1-o(1))n/2 distinct distances -/
@[category research open, AMS 52]
theorem convex_polyhedron_distinct_distances (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (P : Finset (Fin 3 → ℝ)), P.card = n →
        sorry →  -- convex polyhedron condition
        sorry ≥ Nat.floor ((1 - ε) * n / 2) := by
  sorry

end Erdos660
