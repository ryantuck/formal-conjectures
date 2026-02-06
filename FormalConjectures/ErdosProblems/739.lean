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
# Erdős Problem 739

Chromatic cardinal subgraph ladder.

OPEN (NOT PROVABLE - model-dependent)

*Reference:* [erdosproblems.com/739](https://www.erdosproblems.com/739)
-/

open Finset Cardinal

open scoped Topology Real

namespace Erdos739

variable {α : Type*}

/-- Chromatic number (extended to cardinals) -/
noncomputable def chromaticCardinal (G : SimpleGraph α) : Cardinal := sorry

/-- Cardinal subgraph ladder -/
@[category research open, AMS 03]
theorem chromatic_subgraph_ladder (answer : Prop) :
    answer ↔ ∀ (m : Cardinal) (G : SimpleGraph α),
      chromaticCardinal G = m →
      ∀ n : Cardinal, n < m → n.IsInfinite →
        ∃ (S : Set α), ∃ (H : SimpleGraph S),
          chromaticCardinal H = n := by
  sorry

end Erdos739
