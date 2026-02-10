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
# Erdős Problem 986

Ramsey number lower bounds.

OPEN

*Reference:* [erdosproblems.com/986](https://www.erdosproblems.com/986)
-/

open Finset

open scoped Topology Real

namespace Erdos986

/-- Ramsey number R(k,n) -/
noncomputable def R (k n : ℕ) : ℕ := sorry

/-- Lower bound on Ramsey numbers -/
@[category research open, AMS 05]
theorem ramsey_lower_bound (k : ℕ) (hk : 3 ≤ k) (answer : Prop) :
    answer ↔ ∃ (c : ℝ), 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) ^ ((k : ℝ) - 1) / (Real.log n) ^ c ≤ R k n := by
  sorry

end Erdos986
