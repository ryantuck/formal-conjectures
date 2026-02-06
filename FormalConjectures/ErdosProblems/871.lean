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
# Erdős Problem 871

Partition growing basis into two bases.

DISPROVED

*Reference:* [erdosproblems.com/871](https://www.erdosproblems.com/871)
-/

open Finset

open scoped Topology Real

namespace Erdos871

/-- Additive basis of order 2 -/
def IsAdditiveBasis2 (A : Set ℕ) : Prop := sorry

/-- Representation function -/
noncomputable def r (A : Set ℕ) (n : ℕ) : ℕ := sorry

/-- Disproved: growing basis partitions into two bases -/
@[category research solved, AMS 11]
theorem not_partition_growing_basis :
    ¬ ∀ (A : Set ℕ),
      IsAdditiveBasis2 A →
      Filter.Tendsto (r A) Filter.atTop Filter.atTop →
      ∃ (A₁ A₂ : Set ℕ),
        Disjoint A₁ A₂ ∧
        A = A₁ ∪ A₂ ∧
        IsAdditiveBasis2 A₁ ∧
        IsAdditiveBasis2 A₂ := by
  sorry

end Erdos871
