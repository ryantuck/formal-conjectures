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
# Erdős Problem 980

k-th power nonresidue sums.

PROVED

*Reference:* [erdosproblems.com/980](https://www.erdosproblems.com/980)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos980

/-- Least k-th power nonresidue modulo p -/
noncomputable def n_k (k p : ℕ) : ℕ := sorry

/-- Asymptotic for sum of least k-th power nonresidues -/
@[category research solved, AMS 11]
theorem power_nonresidue_sum (k : ℕ) :
    ∃ (c : ℝ), 0 < c ∧
      Tendsto (fun x => ((Finset.filter Nat.Prime (Finset.range x)).sum (fun p => n_k k p) : ℝ) / (x / Real.log x))
        atTop (nhds c) := by
  sorry

end Erdos980
