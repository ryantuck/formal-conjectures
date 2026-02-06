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
# Erdős Problem 784

Reciprocal sum and nondivisibility bound.

SOLVED

*Reference:* [erdosproblems.com/784](https://www.erdosproblems.com/784)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos784

/-- Count integers ≤ x not divisible by any element -/
noncomputable def nondivisibleCount (A : Set ℕ) (x : ℝ) : ℕ := sorry

/-- Affirmative for C ≤ 1, negative for C > 1 -/
@[category research solved, AMS 11]
theorem reciprocal_nondivisibility_C_small (C : ℝ) (hC : 0 < C ∧ C ≤ 1) :
    ∃ c : ℝ, c > 0 ∧
      ∀ (A : Set ℕ), sorry →
        ∀ᶠ (x : ℝ) in Filter.atTop,
          nondivisibleCount A x ≥ x / (Real.log x) ^ c := by
  sorry

end Erdos784
