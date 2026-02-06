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
# Erdős Problem 709

Find good bounds for f(n) - divisibility in consecutive integers.

OPEN (bounds: (log n)^c ≪ f(n) ≪ n^(1/2))

*Reference:* [erdosproblems.com/709](https://www.erdosproblems.com/709)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos709

/-- f(n): minimal value for consecutive integer divisibility -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Current bounds for f(n) -/
@[category research open, AMS 11]
theorem divisibility_consecutive_bounds :
    ∃ c : ℝ, c > 0 ∧
      (∀ᶠ (n : ℕ) in Filter.atTop, (Real.log n) ^ c ≤ f n) ∧
      (∀ᶠ (n : ℕ) in Filter.atTop, f n ≤ (n : ℝ) ^ (1/2 : ℝ)) := by
  sorry

end Erdos709
