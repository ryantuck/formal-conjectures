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
# Erdős Problem 877

Count of maximal sum-free subsets.

PROVED

*Reference:* [erdosproblems.com/877](https://www.erdosproblems.com/877)
-/

open Finset

open scoped Topology Real

namespace Erdos877

/-- Sum-free property -/
def SumFree (A : Finset ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z

/-- f_m(n): count of maximal sum-free subsets -/
noncomputable def f_m (n : ℕ) : ℕ := sorry

/-- f_m(n) = o(2^(n/2)) -/
@[category research solved, AMS 11]
theorem maximal_sum_free_count :
    Filter.Tendsto (fun n => (f_m n : ℝ) / 2 ^ ((n : ℝ) / 2))
      Filter.atTop (nhds 0) := by
  sorry

end Erdos877
