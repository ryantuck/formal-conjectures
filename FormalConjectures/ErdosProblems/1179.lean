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
# Erdős Problem 1179

Subset sum function estimation.

PROVED

*Reference:* [erdosproblems.com/1179](https://www.erdosproblems.com/1179)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1179

/-- Subset sum function estimation in abelian groups -/
@[category research solved, AMS 11]
theorem subset_sum_function_estimation (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (g : ℕ → ℕ),
      ∀ᶠ N in atTop, g N = (1 + sorry) * Real.log N / Real.log 2 := by
  sorry

end Erdos1179
