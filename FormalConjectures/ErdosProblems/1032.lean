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
# Erdős Problem 1032

4-chromatic critical graphs.

OPEN

*Reference:* [erdosproblems.com/1032](https://www.erdosproblems.com/1032)
-/

open Finset

open scoped Topology Real

namespace Erdos1032

variable {α : Type*}

/-- 4-chromatic critical graphs with large minimum degree -/
@[category research open, AMS 05]
theorem four_chromatic_critical (answer : Prop) :
    answer ↔ ∃ (c : ℝ), 0 < c ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, ∃ (G : SimpleGraph (Fin n)),
        G.chromaticNumber = 4 ∧
        (∀ e : Sym2 (Fin n), (G.deleteEdges {e}).chromaticNumber < 4) ∧
        (∀ [DecidableRel G.Adj] (v : Fin n), (G.degree v : ℝ) ≥ c * (n : ℝ)) := by
  sorry

end Erdos1032
