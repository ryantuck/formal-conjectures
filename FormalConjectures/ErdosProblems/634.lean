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
# Erdős Problem 634

Find all n such that some triangle can be cut into exactly n congruent triangles.

OPEN ($25 reward)

*Reference:* [erdosproblems.com/634](https://www.erdosproblems.com/634)
-/

open scoped Topology Real

namespace Erdos634

/-- A triangle can be cut into n congruent triangles -/
def CanBeCutInto (T : Set (Fin 2 → ℝ)) (n : ℕ) : Prop := sorry

/-- Characterize all n for which some triangle dissects into n congruent triangles -/
@[category research open, AMS 52]
theorem triangle_dissection_numbers :
    ∃ S : Set ℕ, ∀ n : ℕ, (∃ T : Set (Fin 2 → ℝ), CanBeCutInto T n) ↔ n ∈ S := by
  sorry

end Erdos634
