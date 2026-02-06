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
# Erdős Problem 955

*Reference:* [erdosproblems.com/955](https://www.erdosproblems.com/955)

## Statement (OPEN)

Let s(n) = σ(n) - n be the sum of proper divisors.

**Conjecture:** If A ⊆ ℕ has density 0, then s⁻¹(A) must also have density 0.

This is a conjecture by Erdős, Granville, Pomerance, and Spiro (1990).
The inverse image can have positive density even when the original set doesn't.

**Partial results:**
- Proven true when A is the set of primes (Pollack)
- Proven for integers with unusually many prime factors (Troupe)
- Proven for sums of two squares (Troupe)
- Pollack, Pomerance, and Thompson: if A has size ≤ x^{1/2+ε(x)} where ε(x)→0,
  then the preimage has density 0

## Source
[EGPS90]
-/

open scoped ArithmeticFunction Topology Real

namespace Erdos955

/-- Natural density of a set of natural numbers -/
noncomputable def density (A : Set ℕ) : ℝ := sorry

/-- Sum of proper divisors function s(n) = σ(n) - n -/
def s (n : ℕ) : ℕ := σ 1 n - n

/-- Main conjecture: If A has density 0, then s⁻¹(A) has density 0 -/
@[category research open, AMS 11]
theorem density_zero_preimage_conjecture :
    ∀ A : Set ℕ, density A = 0 → density (s ⁻¹' A) = 0 := by
  sorry

end Erdos955
