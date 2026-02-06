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
# Erdős Problem 1142

Primes of the form n - 2^k.

OPEN

*Reference:* [erdosproblems.com/1142](https://www.erdosproblems.com/1142)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1142

/-- Infinitely many primes of form n - 2^k -/
@[category research open, AMS 11]
theorem primes_form_n_minus_power_of_two :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ n k : ℕ, p = n - 2^k} := by
  sorry

end Erdos1142
