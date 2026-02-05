/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 540

Is it true that if A ⊆ ℤ/Nℤ has size ≫ N^(1/2), then there exists some non-empty
S ⊆ A such that ∑_{n∈S} n ≡ 0 (mod N)?

SOLVED: Olson (1968) for prime N, Szemerédi (1970) for all N.
Refined: Balandraud showed threshold (2N)^(1/2) for prime N.

*Reference:* [erdosproblems.com/540](https://www.erdosproblems.com/540)
-/

open Finset ZMod

namespace Erdos540

/-- Zero-sum subset exists for dense sets in ℤ/Nℤ -/
@[category research solved, AMS 11]
theorem zero_sum_threshold (N : ℕ) (hN : N > 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ (A : Finset (ZMod N)),
      A.card ≥ ⌊c * Real.sqrt N⌋₊ →
      ∃ (S : Finset (ZMod N)), S ⊆ A ∧ S.Nonempty ∧
        ∑ n ∈ S, n = 0 := by
  sorry

/-- Olson's theorem for prime modulus -/
@[category research solved, AMS 11]
theorem olson_prime (p : ℕ) (hp : p.Prime) :
    ∀ (A : Finset (ZMod p)),
      A.card ≥ ⌈Real.sqrt p⌉₊ →
      ∃ (S : Finset (ZMod p)), S ⊆ A ∧ S.Nonempty ∧
        ∑ n ∈ S, n = 0 := by
  sorry

/-- Balandraud's refined threshold for primes -/
@[category research solved, AMS 11]
theorem balandraud_threshold (p : ℕ) (hp : p.Prime) :
    ∀ (A : Finset (ZMod p)),
      A.card ≥ ⌈Real.sqrt (2 * p)⌉₊ →
      ∃ (S : Finset (ZMod p)), S ⊆ A ∧ S.Nonempty ∧
        ∑ n ∈ S, n = 0 := by
  sorry

/-- Szemerédi's generalization to all moduli -/
@[category research solved, AMS 11]
theorem szemeredi_general (N : ℕ) (hN : N > 0) :
    ∃ f : ℕ → ℕ, (∀ n, f n ≤ ⌈2 * Real.sqrt n⌉₊) ∧
      ∀ (A : Finset (ZMod N)),
        A.card ≥ f N →
        ∃ (S : Finset (ZMod N)), S ⊆ A ∧ S.Nonempty ∧
          ∑ n ∈ S, n = 0 := by
  sorry

end Erdos540
