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

This problem asks whether there are infinitely many primes that can be expressed
as n - 2^k for some natural numbers n and k. This is related to questions about
the distribution of primes in arithmetic progressions and sequences involving
powers of 2.

OPEN

*Reference:* [erdosproblems.com/1142](https://www.erdosproblems.com/1142)
-/

namespace Erdos1142

/-- There exist infinitely many primes of the form n - 2^k where n and k are
    natural numbers. -/
@[category research open, AMS 11]
theorem primes_form_n_minus_power_of_two :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ n k : ℕ, p = n - 2^k} := by
  sorry

end Erdos1142
