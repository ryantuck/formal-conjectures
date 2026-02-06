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
# Erdős Problem 764

Triple convolution error term.

DISPROVED

*Reference:* [erdosproblems.com/764](https://www.erdosproblems.com/764)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos764

/-- h-fold convolution error -/
noncomputable def hConvolutionError (A : Set ℕ) (h N : ℕ) : ℝ := sorry

/-- Disproved for general h-fold convolutions -/
@[category research solved, AMS 11]
theorem not_h_convolution_bounded (h : ℕ) (hh : h ≥ 3) :
    ¬ ∃ C : ℝ, ∀ (A : Set ℕ) (N : ℕ),
      |hConvolutionError A h N| ≤ C := by
  sorry

end Erdos764
