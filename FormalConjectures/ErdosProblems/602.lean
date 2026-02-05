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
# Erdős Problem 602

Let (A_i) be a family of countably infinite sets such that for any i ≠ j, the
intersection A_i ∩ A_j is finite and ≠ 1 (in size). Does there exist a 2-coloring
of ⋃ A_i such that no A_i is monochromatic?

OPEN (Property B)

*Reference:* [erdosproblems.com/602](https://www.erdosproblems.com/602)
-/

open Cardinal

open scoped Topology Real

namespace Erdos602

/-- 2-coloring of countably infinite sets with intersection ≠ 1 has Property B -/
@[category research open, AMS 03 05]
theorem property_b_intersection_not_one (answer : Prop) :
    answer ↔ ∀ (family : ℕ → Set ℕ),
      (∀ i, (family i).Infinite) ∧
      (∀ i j, i ≠ j → (family i ∩ family j).Finite ∧ (family i ∩ family j).ncard ≠ 1) →
      ∃ (coloring : ℕ → Fin 2),
        ∀ i, ∃ a b, a ∈ family i ∧ b ∈ family i ∧ coloring a ≠ coloring b := by
  sorry

end Erdos602
