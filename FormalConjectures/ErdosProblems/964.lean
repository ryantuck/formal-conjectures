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
# Erdős Problem 964

Divisor ratio density.

PROVED

*Reference:* [erdosproblems.com/964](https://www.erdosproblems.com/964)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos964

/-- Divisor ratio is everywhere dense -/
@[category research solved, AMS 11]
theorem divisor_ratio_dense :
    ∀ x > 0, ∀ ε > 0,
      ∃ n : ℕ, |(Nat.divisors (n + 1)).card / (Nat.divisors n).card - x| < ε := by
  sorry

end Erdos964
