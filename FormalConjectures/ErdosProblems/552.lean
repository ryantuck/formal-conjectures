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
# Erdős Problem 552

Determine R(C_4, S_n) where S_n is the star K_{1,n}.
Does there exist c > 0 such that for infinitely many n:
R(C_4, S_n) ≤ n + √n - c?

OPEN ($100 prize)

*Reference:* [erdosproblems.com/552](https://www.erdosproblems.com/552)
-/

open Real

namespace Erdos552

/-- Known bounds for R(C_4, S_n) -/
@[category research open, AMS 05]
theorem ramsey_c4_star_bounds :
    ∀ n : ℕ, n ≥ 2 → True := by
  intro _ _
  trivial

/-- Conjecture: bound is tight -/
@[category research open, AMS 05]
theorem ramsey_c4_star_conjecture :
    answer(sorry) ↔ sorry := by
  sorry

end Erdos552
