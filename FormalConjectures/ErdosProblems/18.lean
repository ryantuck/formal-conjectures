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
# Erdős Problem 18

*Reference:* [erdosproblems.com/18](https://www.erdosproblems.com/18)
-/

namespace Erdos18

open Nat

/--
We call $m$ practical if every integer $1 \leq n < m$ is the sum of distinct divisors of $m$.
-/
def IsPractical (m : ℕ) : Prop :=
  ∀ n, 1 ≤ n → n < m → ∃ d : Finset ℕ, d ⊆ m.divisors ∧ d.sum id = n

/--
If $m$ is practical then let $h(m)$ be such that $h(m)$ many divisors always suffice.
We define it as the minimal such number.
-/
noncomputable def h (m : ℕ) : ℕ :=
  sInf {k | ∀ n, 1 ≤ n → n < m → ∃ d : Finset ℕ, d ⊆ m.divisors ∧ d.sum id = n ∧ d.card ≤ k}

/--
Are there infinitely many practical $m$ such that $h(m) < (\log \log m)^{O(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_18 : answer(sorry) ↔ ∃ C : ℝ,
    {m | IsPractical m ∧ (h m : ℝ) < (Real.log (Real.log m)) ^ C}.Infinite := by
  sorry

/--
Is it true that $h(n!) < n^{o(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_18.variants.factorial_small : answer(sorry) ↔ ∀ ε > 0, ∀ᶠ n : ℕ in Filter.atTop,
    (h (n.factorial) : ℝ) < (n : ℝ) ^ ε := by
  sorry

/--
Is it true that $h(n!) < (\log n)^{O(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_18.variants.factorial_log : answer(sorry) ↔ ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
    (h (n.factorial) : ℝ) < (Real.log n) ^ C := by
  sorry

end Erdos18
