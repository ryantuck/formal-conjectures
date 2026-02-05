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
# Erdős Problem 589

Let g(n) be the maximum size of a subset with no three collinear points that is guaranteed
to exist in any set of n points in R² with no four collinear. Estimate g(n).

OPEN (bounds: n^{1/2} log n to n^{5/6+o(1)})

*Reference:* [erdosproblems.com/589](https://www.erdosproblems.com/589)
-/

open EuclideanSpace

open scoped Topology Real

namespace Erdos589

/-- g(n): max guaranteed non-collinear subset in n-point set with no 4 collinear -/
noncomputable def g (n : ℕ) : ℕ := sorry

/-- Lower bound: g(n) ≥ n^{1/2} log n -/
@[category research open, AMS 52]
theorem g_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (g n : ℝ) ≥ c * (n : ℝ) ^ (1 / 2) * Real.log n := by
  sorry

/-- Upper bound: g(n) ≤ n^{5/6+o(1)} -/
@[category research open, AMS 52]
theorem g_upper_bound :
    ∀ ε > 0, ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (g n : ℝ) ≤ c * (n : ℝ) ^ (5 / 6 + ε) := by
  sorry

end Erdos589
