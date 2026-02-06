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
# Erdős Problem 880

Additive basis with bounded gaps.

PROVED

*Reference:* [erdosproblems.com/880](https://www.erdosproblems.com/880)
-/

open Finset

open scoped Topology Real

namespace Erdos880

/-- Additive basis of order k -/
def IsAdditiveBasisK (A : Set ℕ) (k : ℕ) : Prop := sorry

/-- Distinct element sums have bounded gaps -/
@[category research solved, AMS 11]
theorem additive_basis_bounded_gaps (k : ℕ) :
    ∀ (A : Set ℕ),
      IsAdditiveBasisK A k →
      ∃ C : ℕ, sorry := by
  sorry

end Erdos880
