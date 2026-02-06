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
# Erdős Problem 977

Mersenne number prime divisors.

PROVED

*Reference:* [erdosproblems.com/977](https://www.erdosproblems.com/977)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos977

/-- Greatest prime divisor function -/
noncomputable def P (m : ℕ) : ℕ :=
  (Nat.factors m).maximum?.getD 1

/-- Mersenne numbers have unbounded relative prime divisors -/
@[category research solved, AMS 11]
theorem mersenne_prime_divisor_growth :
    Tendsto (fun n => (P (2 ^ n - 1) : ℝ) / n) atTop atTop := by
  sorry

end Erdos977
