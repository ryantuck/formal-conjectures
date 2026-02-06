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
# Erdős Problem 674

Are there any integer solutions to x^x·y^y = z^z with x,y,z > 1?

PROVED: Ko proved no solutions when gcd(x,y)=1; infinitely many in general

*Reference:* [erdosproblems.com/674](https://www.erdosproblems.com/674)
-/

open Nat

open scoped Topology Real

namespace Erdos674

/-- No coprime solutions to x^x·y^y = z^z -/
@[category research solved, AMS 11]
theorem no_coprime_solutions_power_equation :
    ¬ ∃ x y z : ℕ, x > 1 ∧ y > 1 ∧ z > 1 ∧
      Nat.gcd x y = 1 ∧
      x^x * y^y = z^z := by
  sorry

end Erdos674
