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
# Erdős Problem 748

Cameron-Erdős conjecture - sum-free sets.

PROVED

*Reference:* [erdosproblems.com/748](https://www.erdosproblems.com/748)
-/

open Finset Classical

open scoped Topology Real

namespace Erdos748

/-- Sum-free subset -/
def SumFree (A : Finset ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z

/-- Number of sum-free subsets of {1,...,n} -/
noncomputable def f (n : ℕ) : ℕ :=
  (Finset.range (n+1)).powerset.filter SumFree |>.card

/-- Cameron-Erdős conjecture -/
@[category research solved, AMS 11]
theorem cameron_erdos :
    ∃ c : ℕ → ℝ, Filter.Tendsto
      (fun n => (f n : ℝ) / (c n * 2 ^ ((n : ℝ) / 2)))
      Filter.atTop (nhds 1) := by
  sorry

end Erdos748
