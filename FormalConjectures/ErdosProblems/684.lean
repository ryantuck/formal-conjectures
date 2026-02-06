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
# Erdős Problem 684

For 0 ≤ k ≤ n, write C(n,k) = uv where primes dividing u are in [2,k] and primes
dividing v are in (k,n]. Let f(n) be the smallest k such that u > n². Give bounds for f(n).

OPEN (Tang-ChatGPT: f(n) ≤ n^{30/43+o(1)}; heuristic suggests f(n) ~ 2log n)

*Reference:* [erdosproblems.com/684](https://www.erdosproblems.com/684)
-/

open Nat

open scoped Topology Real

namespace Erdos684

/-- f(n): smallest k where u > n² in binomial decomposition -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Bounds for f(n) -/
@[category research open, AMS 11]
theorem binomial_prime_partition_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      f n ≤ Nat.floor ((n : ℝ) ^ (30/43 + c)) := by
  sorry

end Erdos684
