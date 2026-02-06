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
# Erdős Problem 1010

Triangle count in dense graphs.

PROVED

*Reference:* [erdosproblems.com/1010](https://www.erdosproblems.com/1010)
-/

open Finset

open scoped Topology Real

namespace Erdos1010

variable {α : Type*}

/-- Dense graphs have many triangles -/
@[category research solved, AMS 05]
theorem triangle_count_dense (n t : ℕ) (ht : t < Nat.floor (n / 2)) :
    ∀ (G : SimpleGraph (Fin n)),
      Nat.floor (n ^ 2 / 4) + t ≤ G.edgeFinset.card →
      t * Nat.floor (n / 2) ≤ {T : Finset (Fin n) | T.card = 3 ∧ G.IsClique T}.ncard := by
  sorry

end Erdos1010
