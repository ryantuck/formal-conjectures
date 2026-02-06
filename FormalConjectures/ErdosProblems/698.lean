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
# Erdős Problem 698

Is there h(n) → ∞ such that gcd(C(n,i), C(n,j)) ≥ h(n) for 2 ≤ i < j ≤ n/2?

PROVED by Bergman (2011): lower bound ≈ n^(1/2) · 2^i / i^(3/2)

*Reference:* [erdosproblems.com/698](https://www.erdosproblems.com/698)
-/

open Nat

open scoped Topology Real

namespace Erdos698

/-- GCD of binomial coefficients has unbounded lower bound -/
@[category research solved, AMS 11]
theorem binomial_gcd_unbounded :
    ∃ h : ℕ → ℝ, Filter.Tendsto h Filter.atTop Filter.atTop ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ i j : ℕ,
        2 ≤ i → i < j → j ≤ n/2 →
        (Nat.gcd (Nat.choose n i) (Nat.choose n j) : ℝ) ≥ h n := by
  sorry

end Erdos698
