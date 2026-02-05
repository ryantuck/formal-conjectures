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
# Erdős Problem 620

For K₄-free graph G on n vertices, determine f(n), the minimum size of a triangle-free
induced subgraph that G must contain.

OPEN (bounds: n^{1/2}·(log n)^{1/2}/log(log n) to n^{1/2}·log n)

*Reference:* [erdosproblems.com/620](https://www.erdosproblems.com/620)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos620

/-- f(n): min guaranteed triangle-free induced subgraph size in K₄-free graphs -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Lower bound -/
@[category research open, AMS 05]
theorem f_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (f n : ℝ) ≥ c * Real.sqrt n * Real.sqrt (Real.log n) / Real.log (Real.log n) := by
  sorry

/-- Upper bound -/
@[category research open, AMS 05]
theorem f_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (f n : ℝ) ≤ c * Real.sqrt n * Real.log n := by
  sorry

end Erdos620
