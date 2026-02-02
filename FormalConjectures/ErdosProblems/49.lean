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
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.PrimeCounting

/-!
# Erdős Problem 49

*Reference:* [erdosproblems.com/49](https://www.erdosproblems.com/49)
-/

namespace Erdos49

open scoped BigOperators

/--
Let $A={a_1<...<a_t}\subseteq {1,...,N}$ be such that $\phi(a_1)<...<\phi(a_t)$.
The primes are such an example. Are they the largest possible?
Can one show that $|A|<(1+o(1))\pi(N)$ or even $|A|=o(N)$?

Solved by Tao [Ta23b], who proved that
$$|A| \leq \left(1+O\left(\frac{(\log\log x)^5}{\log x}\right)\right)\pi(x).$$

[Ta23b] T. Tao, _On the number of integers with increasing totient values_, arXiv:2308.15617 (2023).
-/ 
@[category research solved, AMS 11]
theorem erdos_49 : answer(True) ↔ ∀ (ε : ℝ), 0 < ε → ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    ∀ (A : Finset ℕ), ↑A ⊆ Finset.Icc 1 N →
        (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a < Nat.totient b) →
        (A.card : ℝ) < (1 + ε) * Nat.primeCounting N := by
      sorry
    
    /--
    Tao [Ta23b] proved the quantitative bound
    $$|A| \leq \left(1+O\left(\frac{(\log\log x)^5}{\log x}\right)\right)\pi(x).$$
    -/
    @[category research solved, AMS 11]
    theorem erdos_49.variants.tao_bound : ∃ (C : ℝ), ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
        ∀ (A : Finset ℕ), ↑A ⊆ Finset.Icc 1 N →
        (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a < Nat.totient b) →
        (A.card : ℝ) ≤ (1 + C * (Real.log (Real.log N)) ^ 5 / Real.log N) * Nat.primeCounting N := by
      sorry
end Erdos49
