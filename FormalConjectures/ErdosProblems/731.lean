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
# Erdős Problem 731

Least integer m where m ∤ C(2n,n).

OPEN

*Reference:* [erdosproblems.com/731](https://www.erdosproblems.com/731)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos731

/-- Least integer not dividing C(2n,n) -/
noncomputable def m (n : ℕ) : ℕ := sorry

/-- Asymptotic behavior of m(n) -/
@[category research open, AMS 11]
theorem binomial_nondivisor_asymptotic :
    ∃ f : ℕ → ℝ, ∀ᶠ (n : ℕ) in Filter.atTop, m n ~ f n := by
  sorry

end Erdos731
