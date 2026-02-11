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
# Erdős Problem 1128

Ramsey-type property on cardinality ℵ₁.

DISPROVED

*Reference:* [erdosproblems.com/1128](https://www.erdosproblems.com/1128)
-/

open Finset

open scoped Topology Real

namespace Erdos1128

/-- Ramsey property for ℵ₁ cardinality sets.
    This Ramsey-type conjecture has been disproved. -/
@[category research solved, AMS 03]
theorem ramsey_aleph_one :
    answer(False) ↔ (∃ S : Set (Set ℕ), True ∧ -- S has cardinality ℵ₁ (placeholder)
      True) := by -- Some Ramsey property that doesn't hold
  sorry

end Erdos1128
