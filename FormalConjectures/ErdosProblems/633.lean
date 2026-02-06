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
# Erdős Problem 633

Classify all triangles that can only be cut into a square number of congruent triangles.

OPEN ($25 reward)

*Reference:* [erdosproblems.com/633](https://www.erdosproblems.com/633)
-/

open scoped Topology Real

namespace Erdos633

/-- A triangle can be cut into n congruent triangles -/
def CanBeCutInto (T : Set (Fin 2 → ℝ)) (n : ℕ) : Prop := sorry

/-- Classify triangles cuttable only into square number of congruent triangles -/
@[category research open, AMS 52]
theorem triangle_square_dissection (T : Set (Fin 2 → ℝ)) :
    (∀ n : ℕ, CanBeCutInto T n → ∃ k : ℕ, n = k^2) →
    sorry := by
  sorry

end Erdos633
