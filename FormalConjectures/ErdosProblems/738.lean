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
# Erdős Problem 738

Triangle-free infinite chromatic contains all trees.

OPEN

*Reference:* [erdosproblems.com/738](https://www.erdosproblems.com/738)
-/

open Finset

open scoped Topology Real

namespace Erdos738

variable {α β : Type*}

/-- Chromatic number -/
noncomputable def chromaticNumber (G : SimpleGraph α) : ℕ∞ := sorry

/-- Contains induced subgraph -/
def containsInducedSubgraph (G : SimpleGraph α) (H : SimpleGraph β) : Prop := sorry

/-- Triangle-free infinite chromatic contains all trees -/
@[category research open, AMS 05]
theorem triangle_free_contains_trees (answer : Prop) :
    answer ↔ ∀ (G : SimpleGraph α),
      chromaticNumber G = ⊤ →
      G.CliqueFree 3 →
      ∀ (T : SimpleGraph β), T.IsTree →
        containsInducedSubgraph G T := by
  sorry

end Erdos738
