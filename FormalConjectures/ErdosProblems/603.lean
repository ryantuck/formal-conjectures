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
# Erdős Problem 603

Let (A_i) be a family of countably infinite sets such that |A_i ∩ A_j| ≠ 2 for all i ≠ j.
Find the smallest cardinal C such that ⋃ A_i can always be colored with at most C colors
so that no A_i is monochromatic.

OPEN

*Reference:* [erdosproblems.com/603](https://www.erdosproblems.com/603)
-/

open Cardinal

open scoped Topology Real

namespace Erdos603

/-- Min cardinal for coloring sets with intersection ≠ 2 -/
@[category research open, AMS 03 05]
theorem min_cardinal_intersection_not_two :
    ∃ (C : Cardinal),
      (∀ (family : ℕ → Set ℕ),
        (∀ i, (family i).Infinite) ∧
        (∀ i j, i ≠ j → (family i ∩ family j).ncard ≠ 2) →
        ∃ (coloring : ℕ → Fin sorry), sorry) ∧
      (∀ C' < C, ∃ (family : ℕ → Set ℕ), sorry) := by
  sorry

end Erdos603
