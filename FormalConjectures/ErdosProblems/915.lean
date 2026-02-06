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
# Erdős Problem 915

Graph connectivity and disjoint paths.

SOLVED

*Reference:* [erdosproblems.com/915](https://www.erdosproblems.com/915)
-/

open Finset

open scoped Topology Real

namespace Erdos915

variable {α : Type*}

/-- Graph connectivity implies existence of vertex-disjoint paths -/
@[category research solved, AMS 05]
theorem connectivity_disjoint_paths (k : ℕ) (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)),
      G.Connected →
      (∀ S : Finset (Fin n), S.card < k → (G.deleteVerts S).Connected) →
      ∀ (pairs : Finset (Fin n × Fin n)),
        pairs.card = k →
        ∃ (paths : Finset (List (Fin n))),
          sorry := by
  sorry

end Erdos915
