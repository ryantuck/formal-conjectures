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
# Erdős Problem 456

Let pₙ be the smallest prime ≡ 1 (mod n) and let mₙ be the smallest integer such that
n | φ(mₙ).

Questions:
1. Is mₙ < pₙ for almost all n?
2. Does pₙ/mₙ → ∞ for almost all n?
3. Are there infinitely many primes p such that p-1 is the only n with mₙ = p?

Linnik: pₙ ≤ n^O(1).
Trivial: mₙ ≤ pₙ always.
Erdős: For infinitely many n, mₙ < pₙ.

*Reference:* [erdosproblems.com/456](https://www.erdosproblems.com/456)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos456

/-- pₙ is the smallest prime ≡ 1 (mod n) -/
noncomputable def p_n (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p % n = 1}

/-- mₙ is the smallest m with n | φ(m) -/
noncomputable def m_n (n : ℕ) : ℕ :=
  sInf {m : ℕ | m > 0 ∧ n ∣ m.totient}

/-- Question 1: mₙ < pₙ for almost all n -/
@[category research open, AMS 11]
theorem erdos_456_q1 :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      (Nat.card {n ≤ N | m_n n < p_n n} : ℝ) > (1 - ε) * N := by
  sorry

/-- Question 2: pₙ/mₙ → ∞ for almost all n -/
@[category research open, AMS 11]
theorem erdos_456_q2 :
    ∀ M : ℝ, M > 0 → ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      (Nat.card {n ≤ N | (p_n n : ℝ) / (m_n n : ℝ) > M} : ℝ) > (1 - ε) * N := by
  sorry

end Erdos456
