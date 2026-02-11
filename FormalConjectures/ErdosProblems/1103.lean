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
# Erdős Problem 1103

Growth rate of sequences with squarefree sumsets.

OPEN

*Reference:* [erdosproblems.com/1103](https://www.erdosproblems.com/1103)
-/

open Finset Filter

open scoped Real

namespace Erdos1103

/-- Lower bound on growth: any infinite sequence with squarefree sumset
    must grow at least as fast as j^{4/3}. -/
@[category research open, AMS 11]
theorem squarefree_sumset_growth_lower :
    ∀ (A : ℕ → ℕ), StrictMono A →
      (∀ i j, Squarefree (A i + A j)) →
        ∃ c > 0, ∀ᶠ j in atTop, (A j : ℝ) ≥ c * (j : ℝ) ^ ((4 : ℝ) / 3) := by
  sorry

/-- Upper bound on growth: there exists an infinite squarefree-sumset sequence
    growing at most exponentially (sub-exponentially in a precise sense). -/
@[category research open, AMS 11]
theorem squarefree_sumset_growth_upper :
    ∃ (A : ℕ → ℕ), StrictMono A ∧
      (∀ i j, Squarefree (A i + A j)) ∧
        ∀ᶠ j in atTop, (A j : ℝ) < Real.exp (5 * j / Real.log j) := by
  sorry

end Erdos1103
