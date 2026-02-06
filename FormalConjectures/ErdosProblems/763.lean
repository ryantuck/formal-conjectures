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
# Erdős Problem 763

Erdős-Turán conjecture on convolution error.

DISPROVED

*Reference:* [erdosproblems.com/763](https://www.erdosproblems.com/763)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos763

/-- Convolution error term -/
noncomputable def convolutionError (A : Set ℕ) (N : ℕ) : ℝ := sorry

/-- Disproved: error term is O(1) -/
@[category research solved, AMS 11]
theorem not_convolution_error_bounded :
    ¬ ∃ C : ℝ, ∀ (A : Set ℕ) (N : ℕ),
      |convolutionError A N| ≤ C := by
  sorry

/-- Error term cannot be o(N^(1/4)) -/
@[category research solved, AMS 11]
theorem convolution_error_lower_bound :
    ∀ (A : Set ℕ), ∀ᶠ (N : ℕ) in Filter.atTop,
      |convolutionError A N| ≥ sorry * (N : ℝ) ^ (1/4 : ℝ) := by
  sorry

end Erdos763
