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
# Erdős Problem 1100

Properties of τ⊥(n) - coprime consecutive divisors.

OPEN

*Reference:* [erdosproblems.com/1100](https://www.erdosproblems.com/1100)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1100

/-- Number of distinct prime factors -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- Number of coprime consecutive divisor pairs -/
noncomputable def τ_perp (n : ℕ) : ℕ := sorry

/-- Coprime consecutive divisors grow with distinct prime factors -/
@[category research open, AMS 11]
theorem coprime_consecutive_divisors (answer : Prop) :
    answer ↔ Tendsto (fun n : ℕ => (τ_perp n : ℝ) / omega n) atTop atTop ∧
      (∀ n, (τ_perp n : ℝ) < Real.exp ((Real.log (n : ℝ)) ^ ((1 : ℝ)/2))) := by
  sorry

end Erdos1100
