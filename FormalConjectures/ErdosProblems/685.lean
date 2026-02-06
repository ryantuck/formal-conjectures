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
# Erdős Problem 685

For large n and ε > 0, for all n^ε < k ≤ n^{1-ε}, does the number of distinct prime
divisors of C(n,k) equal (1+o(1))k Σ_{k<p<n} 1/p? Or even for k ≥ (log n)^c?

OPEN

*Reference:* [erdosproblems.com/685](https://www.erdosproblems.com/685)
-/

open Nat

open scoped Topology Real

namespace Erdos685

/-- Number of distinct prime divisors of C(n,k) -/
noncomputable def ω_binomial (n k : ℕ) : ℕ := sorry

/-- Prime sum in range -/
noncomputable def primeSumRange (k n : ℕ) : ℝ :=
  sorry  -- Σ_{k<p<n, p prime} 1/p

/-- ω(C(n,k)) ~ k Σ_{k<p<n} 1/p for n^ε < k ≤ n^{1-ε} -/
@[category research open, AMS 11]
theorem binomial_prime_divisor_count (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ k : ℕ, (n : ℝ)^ε < k ∧ k ≤ (n : ℝ)^(1-ε) →
        ∃ δ : ℝ, δ > 0 ∧
          |((ω_binomial n k : ℝ) - k * primeSumRange k n)| < δ * k * primeSumRange k n := by
  sorry

end Erdos685
