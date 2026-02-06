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
# Erdős Problem 651

Is f_k(n) > (1+c_k)^n for points in convex position?

DISPROVED by Pohoata and Zakharov: f_3(n) ≤ 2^o(n)

*Reference:* [erdosproblems.com/651](https://www.erdosproblems.com/651)
-/

open Finset

open scoped Topology Real

namespace Erdos651

/-- f_k(n) for points in convex position -/
noncomputable def f_k (k n : ℕ) : ℕ := sorry

/-- Negation: f_3(n) ≤ 2^o(n) -/
@[category research solved, AMS 52]
theorem not_exponential_convex_position :
    ¬ ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      f_k 3 n > ((1 + c) ^ n : ℝ) := by
  sorry

end Erdos651
