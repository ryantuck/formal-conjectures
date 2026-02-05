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
# Erdős Problem 467

For all sufficiently large x, can we:
1. Choose congruence classes aₚ for each prime p ≤ x
2. Partition primes {p ≤ x} into two non-empty sets A and B
3. For every integer n < x, there exists p ∈ A and q ∈ B such that
   n ≡ aₚ (mod p) and n ≡ a_q (mod q)?

*Reference:* [erdosproblems.com/467](https://www.erdosproblems.com/467)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos467

/-- Erdős-Graham conjecture -/
@[category research open, AMS 11]
theorem erdos_467 :
    ∀ᶠ x : ℕ in atTop, ∃ (a : ∀ p : ℕ, ZMod p) (A B : Finset ℕ),
      A.Nonempty ∧ B.Nonempty ∧ A ∩ B = ∅ ∧
      (∀ p ∈ A, p.Prime ∧ p ≤ x) ∧ (∀ q ∈ B, q.Prime ∧ q ≤ x) ∧
      ∀ n : ℕ, n < x →
        ∃ p ∈ A, ∃ q ∈ B, (n : ZMod p) = a p ∧ (n : ZMod q) = a q := by
  sorry

end Erdos467
