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
# Erdős Problem 639

When K_n is 2-colored, at most n²/4 edges are not in a monochromatic triangle?

SOLVED by Keevash and Sudakov

*Reference:* [erdosproblems.com/639](https://www.erdosproblems.com/639)
-/

open SimpleGraph Finset

open scoped Topology Real

namespace Erdos639

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- At most n²/4 edges not in monochromatic triangle when K_n is 2-colored -/
@[category research solved, AMS 05]
theorem two_coloring_monochromatic_triangles (n : ℕ) :
    ∀ (coloring : Fin n × Fin n → Fin 2),
      sorry ≤ n^2 / 4 := by
  sorry

end Erdos639
