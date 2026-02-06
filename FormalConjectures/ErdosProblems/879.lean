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
# Erdős Problem 879

Admissible sets - maximum sum G(n).

OPEN

*Reference:* [erdosproblems.com/879](https://www.erdosproblems.com/879)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos879

/-- Admissible set (pairwise coprime) -/
def IsAdmissible (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → Nat.gcd a b = 1

/-- G(n): maximum sum of admissible subset -/
noncomputable def G (n : ℕ) : ℕ := sorry

/-- Bounds on G(n) and prime factor requirements -/
@[category research open, AMS 11]
theorem admissible_sum_bounds :
    sorry := by
  sorry

end Erdos879
