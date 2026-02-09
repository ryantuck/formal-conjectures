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
# Erdős Problem 810

Graph colorable with C₄ rainbow.

OPEN

*Reference:* [erdosproblems.com/810](https://www.erdosproblems.com/810)
-/

open Finset

open scoped Topology Real

namespace Erdos810

/-- Graph with εn² edges colorable with C₄ rainbow -/
@[category research open, AMS 05]
theorem c4_rainbow_coloring (ε : ℝ) (hε : ε > 0) (answer : Prop) :
    answer ↔ ∀ (n : ℕ),
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        (G.edgeFinset.card : ℝ) ≥ ε * (n : ℝ) ^ 2 ∧
        ∃ (c : Sym2 (Fin n) → Fin n),
          True := by
  sorry

end Erdos810
