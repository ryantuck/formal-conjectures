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
# Erdős Problem 787

Maximal sum-free subset g(n).

OPEN

*Reference:* [erdosproblems.com/787](https://www.erdosproblems.com/787)
-/

open Finset

open scoped Topology Real

namespace Erdos787

/-- Sum-free property -/
def SumFree (A : Finset ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z

/-- g(n): maximal sum-free subset size -/
noncomputable def g (n : ℕ) : ℕ := sorry

/-- Bounds for g(n) -/
@[category research open, AMS 11]
theorem sum_free_bound :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ (n : ℕ) (A : Finset ℕ),
        A.card = n →
        ∃ (B : Finset ℕ), B ⊆ A ∧ SumFree B ∧
          B.card ≥ g n ∧ sorry := by
  sorry

end Erdos787
