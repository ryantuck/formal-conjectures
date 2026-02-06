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
# Erdős Problem 842

Graph with triangles and Hamiltonian cycle.

SOLVED

*Reference:* [erdosproblems.com/842](https://www.erdosproblems.com/842)
-/

open Finset

open scoped Topology Real

namespace Erdos842

/-- Graph with n triangles and Hamiltonian cycle has χ ≤ 3 -/
@[category research solved, AMS 05]
theorem triangles_hamiltonian_chromatic :
    ∀ (n : ℕ) (G : SimpleGraph (Fin (3 * n))) [DecidableRel G.Adj],
      (∃ (T : Finset (Finset (Fin (3 * n)))),
        T.card = n ∧
        (∀ t ∈ T, t.card = 3) ∧
        sorry) →
      (∃ (C : sorry), sorry) →
      sorry := by
  sorry

end Erdos842
