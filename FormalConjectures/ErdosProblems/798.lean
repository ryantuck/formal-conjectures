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
# Erdős Problem 798

Minimum points covering grid.

PROVED

*Reference:* [erdosproblems.com/798](https://www.erdosproblems.com/798)
-/

open Finset

open scoped Topology Real

namespace Erdos798

/-- t(n): minimum points in {1,...,n}² covering all points -/
noncomputable def t (n : ℕ) : ℕ := sorry

/-- t(n) ≪ n^(2/3) log n -/
@[category research solved, AMS 52]
theorem grid_covering_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ), t n ≤ C * (n : ℝ) ^ (2/3 : ℝ) * Real.log n := by
  sorry

end Erdos798
