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
# Erdős Problem 740

Chromatic subgraph without short odd cycles.

OPEN

*Reference:* [erdosproblems.com/740](https://www.erdosproblems.com/740)
-/

open Finset Cardinal

open scoped Topology Real

namespace Erdos740

variable {α : Type*}

/-- Chromatic number (extended to cardinals) -/
noncomputable def chromaticCardinal (G : SimpleGraph α) : Cardinal := sorry

/-- Contains odd cycle of length ≤ r -/
def containsOddCycle (G : SimpleGraph α) (r : ℕ) : Prop := sorry

/-- Subgraph without short odd cycles -/
@[category research open, AMS 05]
theorem chromatic_subgraph_no_short_odd_cycles (m : Cardinal) (r : ℕ) (hr : r ≥ 1) (answer : Prop) :
    answer ↔ ∀ (G : SimpleGraph α),
      chromaticCardinal G = m →
      ∃ (S : Set α), ∃ (H : SimpleGraph S),
        chromaticCardinal H = m ∧
        ¬containsOddCycle H r := by
  sorry

end Erdos740
