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
# Erdős Problem 1120

Path length in polynomial level set.

OPEN

*Reference:* [erdosproblems.com/1120](https://www.erdosproblems.com/1120)
-/

open Finset

open scoped Real

namespace Erdos1120

/-- Path length in polynomial level set.
    Asks about bounds on the total path length in level sets of polynomials. -/
@[category research open, AMS 30]
theorem path_length_polynomial_level_set (P : Polynomial ℂ) (c : ℂ) :
    ∃ (L : ℝ), 0 ≤ L ∧
      (∀ path : ℝ → ℂ, (∀ t, P.eval (path t) = c) →
        True) ∧ -- Placeholder for path length bound condition
      L ≤ (P.natDegree : ℝ) * (1 + ‖c‖) := by
  sorry

end Erdos1120
