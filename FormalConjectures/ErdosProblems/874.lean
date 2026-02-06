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
# Erdős Problem 874

Maximum set with disjoint r-fold sumsets.

PROVED (conjectured k(N) ~ 2N^(1/2))

*Reference:* [erdosproblems.com/874](https://www.erdosproblems.com/874)
-/

open Finset

open scoped Topology Real

namespace Erdos874

/-- r-fold sumset -/
def sumsetR (A : Finset ℕ) (r : ℕ) : Finset ℕ := sorry

/-- k(N): maximum |A| with disjoint r-fold sumsets -/
noncomputable def k (N : ℕ) : ℕ := sorry

/-- k(N) ~ 2N^(1/2) -/
@[category research solved, AMS 11]
theorem disjoint_sumsets_asymptotic :
    Filter.Tendsto (fun N => (k N : ℝ) / (2 * (N : ℝ) ^ (1/2 : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

end Erdos874
