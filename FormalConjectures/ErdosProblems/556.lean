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
# Erdős Problem 556

Let R(C_n;3) be minimal m such that if edges of K_m are 3-colored, there's a
monochromatic C_n. Prove R(C_n;3) ≤ 4n - 3.

DECIDABLE (verified for sufficiently large n)

*Reference:* [erdosproblems.com/556](https://www.erdosproblems.com/556)
-/

namespace Erdos556

/-- Three-color cycle Ramsey bound -/
@[category research solved, AMS 05]
theorem three_color_cycle_bound :
    ∀ᶠ (n : ℕ) in Filter.atTop, sorry := by
  sorry

end Erdos556
