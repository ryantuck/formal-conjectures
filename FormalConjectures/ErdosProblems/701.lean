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
# Erdős Problem 701

For set families closed under subsets, does intersecting subfamily inequality hold?

OPEN

*Reference:* [erdosproblems.com/701](https://www.erdosproblems.com/701)
-/

open Finset

open scoped Topology Real

namespace Erdos701

/-- Set family closed under subsets -/
def ClosedUnderSubsets (F : Finset (Finset ℕ)) : Prop :=
  ∀ A B, A ∈ F → B ⊆ A → B ∈ F

/-- Intersecting subfamily inequality -/
@[category research open, AMS 05]
theorem intersecting_subfamily_inequality (answer : Prop) :
    answer ↔ ∀ (F : Finset (Finset ℕ)),
      ClosedUnderSubsets F →
      sorry := by
  sorry

end Erdos701
