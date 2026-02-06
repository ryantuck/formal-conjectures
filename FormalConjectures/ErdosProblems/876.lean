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
# Erdős Problem 876

Infinite sum-free set - gap size.

OPEN

*Reference:* [erdosproblems.com/876](https://www.erdosproblems.com/876)
-/

open Finset

open scoped Topology Real

namespace Erdos876

/-- Sum-free property -/
def SumFree (A : Set ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z

/-- Gap size in infinite sum-free set -/
@[category research open, AMS 11]
theorem sum_free_gap_size (answer : Prop) :
    answer ↔ ∃ (a : ℕ → ℕ), StrictMono a ∧
      SumFree {a n | n : ℕ} ∧
      ∀ n : ℕ, a (n + 1) - a n < n := by
  sorry

end Erdos876
