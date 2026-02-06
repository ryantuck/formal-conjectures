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
# Erdős Problem 792

Maximal f(n) for sum-free subsets.

OPEN (best bound f(n) ≥ n/3 + c log log n)

*Reference:* [erdosproblems.com/792](https://www.erdosproblems.com/792)
-/

open Finset

open scoped Topology Real

namespace Erdos792

/-- Sum-free property -/
def SumFree (A : Finset ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z

/-- f(n): maximum sum-free subset size -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Current best lower bound -/
@[category research open, AMS 11]
theorem sum_free_lower_bound :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        f n ≥ n / 3 + c * Real.log (Real.log n) := by
  sorry

end Erdos792
