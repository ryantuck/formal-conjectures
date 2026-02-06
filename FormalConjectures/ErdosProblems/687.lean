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
# Erdős Problem 687

Let Y(x) be the maximal y such that there exists a choice of congruence classes a_p
for all primes p ≤ x such that every integer in [1,y] is congruent to at least one
of the a_p (mod p). Give good estimates for Y(x). Can one prove Y(x) = o(x²) or even
Y(x) ≪ x^{1+o(1)}?

OPEN ($1000 reward; Y(x) ≪ x²; Y(x) ≫ x(log x log log log x)/log log x)

*Reference:* [erdosproblems.com/687](https://www.erdosproblems.com/687)
-/

open Nat

open scoped Topology Real

namespace Erdos687

/-- Y(x): maximal y for covering congruences -/
noncomputable def Y (x : ℕ) : ℕ := sorry

/-- Is Y(x) = o(x²)? -/
@[category research open, AMS 11]
theorem covering_congruences_bound (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (x : ℕ) in Filter.atTop,
      (Y x : ℝ) < ε * (x : ℝ)^2 := by
  sorry

/-- Upper bound Y(x) ≪ x² -/
@[category research open, AMS 11]
theorem covering_congruences_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ x : ℕ,
      (Y x : ℝ) ≤ c * (x : ℝ)^2 := by
  sorry

end Erdos687
