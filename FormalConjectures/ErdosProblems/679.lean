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
# Erdős Problem 679

Let ω(n) denote distinct prime factors. Are there infinitely many n such that
ω(n-k) < (1+ε)log k/log log k for all large k < n?

OPEN (stronger version with ω(n-k) < log k/log log k + O(1) disproved)

*Reference:* [erdosproblems.com/679](https://www.erdosproblems.com/679)
-/

open Nat

open scoped Topology Real

namespace Erdos679

/-- ω(n): number of distinct prime divisors -/
noncomputable def ω (n : ℕ) : ℕ := sorry

/-- Infinitely many n with ω(n-k) < (1+ε)log k/log log k for all large k < n -/
@[category research open, AMS 11]
theorem infinitely_many_small_omega_predecessors (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ M : ℕ, ∃ n > M,
      ∀ᶠ k in Filter.atTop,
        k < n →
        (ω (n - k) : ℝ) < (1 + ε) * Real.log k / Real.log (Real.log k) := by
  sorry

end Erdos679
