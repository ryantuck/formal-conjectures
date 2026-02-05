/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 555

Determine R(C_{2n};k) where C_{2n} is an even cycle.
Known: k^(1+1/(2n)) ≪ R(C_{2n};k) ≪ k^(1+1/(n-1))

OPEN

*Reference:* [erdosproblems.com/555](https://www.erdosproblems.com/555)
-/

namespace Erdos555

/-- Bounds for even cycle multicolor Ramsey number -/
@[category research open, AMS 05]
theorem even_cycle_ramsey_bounds (n k : ℕ) (hn : n ≥ 2) (hk : k ≥ 2) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ sorry := by
  sorry

end Erdos555
