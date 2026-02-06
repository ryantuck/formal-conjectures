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
# Erdős Problem 649

For primes p,q, does there exist n with P(n)=p and P(n+1)=q?

DISPROVED: counterexamples exist

*Reference:* [erdosproblems.com/649](https://www.erdosproblems.com/649)
-/

open Nat

open scoped Topology Real

namespace Erdos649

/-- P(n): largest prime factor of n -/
noncomputable def P (n : ℕ) : ℕ := sorry

/-- Not all prime pairs can be consecutive largest prime factors -/
@[category research solved, AMS 11]
theorem not_all_prime_pairs_consecutive :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime →
      ∃ n : ℕ, P n = p ∧ P (n+1) = q := by
  sorry

end Erdos649
