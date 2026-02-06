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
# Erdős Problem 862

Count of maximal Sidon subsets.

SOLVED

*Reference:* [erdosproblems.com/862](https://www.erdosproblems.com/862)
-/

open Finset

open scoped Topology Real

namespace Erdos862

/-- A₁(N): count of maximal Sidon subsets of {1,...,N} -/
noncomputable def A1 (N : ℕ) : ℕ := sorry

/-- Lower bound established -/
@[category research solved, AMS 11]
theorem maximal_sidon_count_lower :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (N : ℕ) in Filter.atTop,
        A1 N ≥ 2 ^ ((N : ℝ) ^ c) := by
  sorry

end Erdos862
