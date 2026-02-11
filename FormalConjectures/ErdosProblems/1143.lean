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
# Erdős Problem 1143

Estimation of F_k(p₁,...,p_u) for multiples of primes in intervals.

This problem concerns estimating a function F_k(p₁,...,p_u) that counts or measures
multiples of given primes p₁,...,p_u within certain intervals. The specific
estimation bounds and the exact definition of F_k require further investigation
of the original source.

OPEN

*Reference:* [erdosproblems.com/1143](https://www.erdosproblems.com/1143)
-/

namespace Erdos1143

/-- Estimation for multiples of primes in intervals. The function F_k and its
    properties require precise formulation from the original problem statement. -/
@[category research open, AMS 11]
theorem prime_multiples_in_intervals :
    ∃ (F : ℕ → List ℕ → ℕ), ∀ k : ℕ, ∀ primes : List ℕ,
      (∀ p ∈ primes, Nat.Prime p) →
      answer(sorry) = F k primes := by
  sorry

end Erdos1143
