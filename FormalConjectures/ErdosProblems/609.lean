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
# Erdős Problem 609

For n-edge-colorings of K_{2^n+1}, determine the minimal length f(n) of the longest
monochromatic odd cycle that must appear.

OPEN (bounds: 2^{c√(log n)} to n^{3/2}·2^{n/2})

*Reference:* [erdosproblems.com/609](https://www.erdosproblems.com/609)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos609

/-- f(n): min length of longest monochromatic odd cycle in n-edge-colorings of K_{2^n+1} -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Lower bound -/
@[category research open, AMS 05]
theorem f_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (f n : ℝ) ≥ 2 ^ (c * Real.sqrt (Real.log n)) := by
  sorry

/-- Upper bound -/
@[category research open, AMS 05]
theorem f_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      (f n : ℝ) ≤ c * (n : ℝ) ^ (3 / 2) * 2 ^ ((n : ℝ) / 2) := by
  sorry

end Erdos609
