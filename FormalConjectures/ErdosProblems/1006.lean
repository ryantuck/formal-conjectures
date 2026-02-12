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
# Erdős Problem 1006

Graph edge orientation with girth constraint.

DISPROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1006](https://www.erdosproblems.com/1006)
-/

open Finset

open scoped Topology Real

namespace Erdos1006

variable {α : Type*}

/-- English version: Disproved: edge orientation avoiding cycles and near-cycles -/@[category research solved, AMS 05]
theorem not_edge_orientation_girth :
    ¬ ∀ (G : SimpleGraph α) [Fintype α],
      G.girth > 4 →
      ∃ (orient : α → α → Prop),
        (∀ e : α × α, G.Adj e.1 e.2 → orient e.1 e.2 ∨ orient e.2 e.1) ∧
        sorry := by
  sorry

end Erdos1006
