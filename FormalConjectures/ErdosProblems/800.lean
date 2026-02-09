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
# Erdős Problem 800

Ramsey number for graphs with restricted adjacency.

PROVED

*Reference:* [erdosproblems.com/800](https://www.erdosproblems.com/800)
-/

open Finset

open scoped Topology Real

namespace Erdos800

variable {α : Type*}

/-- Ramsey number -/
noncomputable def ramseyNumber (G : SimpleGraph α) : ℕ := sorry

/-- R(G) ≪ n for graphs with no adjacent degree ≥3 vertices -/
@[category research solved, AMS 05]
theorem ramsey_restricted_adjacency :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [G.LocallyFinite],
        (∀ u v : Fin n, G.Adj u v →
          G.degree u < 3 ∨ G.degree v < 3) →
        ramseyNumber G ≤ C * n := by
  sorry

end Erdos800
