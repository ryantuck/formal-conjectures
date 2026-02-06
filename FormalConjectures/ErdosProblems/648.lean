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
# Erdős Problem 648

Estimate g(n) for longest decreasing sequence of greatest prime factors.

SOLVED: g(n) ≍ √(n/log n) by Cambie

*Reference:* [erdosproblems.com/648](https://www.erdosproblems.com/648)
-/

open Nat

open scoped Topology Real

namespace Erdos648

/-- g(n): longest decreasing sequence of greatest prime factors -/
noncomputable def g (n : ℕ) : ℕ := sorry

/-- g(n) ≍ √(n/log n) -/
@[category research solved, AMS 11]
theorem longest_decreasing_prime_factors :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        c₁ * Real.sqrt (n / Real.log n) ≤ g n ∧
        g n ≤ c₂ * Real.sqrt (n / Real.log n) := by
  sorry

end Erdos648
