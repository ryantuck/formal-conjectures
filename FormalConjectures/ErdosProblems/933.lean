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
# Erdős Problem 933

Growth of prime power divisors in n(n+1).

OPEN

*Reference:* [erdosproblems.com/933](https://www.erdosproblems.com/933)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos933

/-- Largest prime power exponent dividing n(n+1) -/
noncomputable def maxPrimePowerExp (n : ℕ) : ℕ :=
  (n.primeFactors ∪ (n + 1).primeFactors).sup (fun p => Nat.log p (n * (n + 1)))

/-- Growth rate of largest prime power dividing n(n+1) -/
@[category research open, AMS 11]
theorem prime_power_product_growth (answer : Prop) :
    answer ↔ Tendsto (fun n => (maxPrimePowerExp n : ℝ) / Real.log n)
      atTop atTop := by
  sorry

end Erdos933
