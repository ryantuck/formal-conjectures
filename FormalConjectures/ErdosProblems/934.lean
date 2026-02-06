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
# Erdős Problem 934

Graph edge distance problem.

OPEN

*Reference:* [erdosproblems.com/934](https://www.erdosproblems.com/934)
-/

open Finset

open scoped Topology Real

namespace Erdos934

variable {α : Type*}

/-- Edge distance chromatic number bound -/
@[category research open, AMS 05]
theorem edge_distance_chromatic (answer : Prop) :
    answer ↔ ∀ (G : SimpleGraph α) [Fintype α],
      ∃ (k : ℕ), sorry := by
  sorry

end Erdos934
