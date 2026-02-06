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
# Erdős Problem 710

Find asymptotic formula for f(n) - divisibility interval.

OPEN (2000 rupees reward)

*Reference:* [erdosproblems.com/710](https://www.erdosproblems.com/710)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos710

/-- f(n): minimal interval length for divisibility property -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Asymptotic formula for f(n) -/
@[category research open, AMS 11]
theorem divisibility_interval_asymptotic :
    ∃ g : ℕ → ℝ, ∀ᶠ (n : ℕ) in Filter.atTop, f n ~ g n := by
  sorry

end Erdos710
