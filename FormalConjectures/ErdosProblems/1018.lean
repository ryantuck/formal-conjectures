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
# Erdős Problem 1018

Non-planar subgraph existence.

SOLVED

*Reference:* [erdosproblems.com/1018](https://www.erdosproblems.com/1018)
-/

open Finset

open scoped Topology Real

namespace Erdos1018

variable {α : Type*}

/-- Dense graphs contain small non-planar subgraphs -/
@[category research solved, AMS 05]
theorem nonplanar_subgraph (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : ℝ → ℕ),
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (n : ℝ) ^ (1 + ε) ≤ G.edgeFinset.card →
        ∃ (H : SimpleGraph (Fin (f ε))),
          H ≤ G ∧ ¬ H.IsPlanar := by
  sorry

end Erdos1018
