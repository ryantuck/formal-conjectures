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
# Erdős Problem 1123

Boolean algebra isomorphism.

OPEN

*Reference:* [erdosproblems.com/1123](https://www.erdosproblems.com/1123)
-/

open Finset

open scoped Real

namespace Erdos1123

/-- Let B_1 be the Boolean algebra of sets of integers modulo sets of density 0,
    and B_2 be the Boolean algebra of sets modulo sets of logarithmic density 0.
    Are B_1 and B_2 non-isomorphic?
    Under CH they are isomorphic (Just and Krawczyk 1984); without CH, the question is open. -/
@[category research open, AMS 03]
theorem boolean_algebra_isomorphism :
    let densityZeroIdeal : Ideal (Set ℕ) := sorry
    let logDensityZeroIdeal : Ideal (Set ℕ) := sorry
    let B1 := sorry
    let B2 := sorry
    answer(sorry) ↔ ¬ Nonempty (B1 ≃o B2) := by
  sorry

end Erdos1123
