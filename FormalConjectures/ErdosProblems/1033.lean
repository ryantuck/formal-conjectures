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
# Erdős Problem 1033

Triangle degree sum.

OPEN

*Reference:* [erdosproblems.com/1033](https://www.erdosproblems.com/1033)
-/

open Finset

open scoped Topology Real

namespace Erdos1033

variable {α : Type*}

/-- Degree sum bound for triangles in dense graphs -/
noncomputable def h (n : ℕ) : ℕ := sorry

@[category research open, AMS 05]
theorem triangle_degree_sum (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card ≥ n^2 / 4 →
      ∃ (u v w : Fin n), G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧
        G.degree u + G.degree v + G.degree w ≥ h n := by
  sorry

end Erdos1033
