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
# Erdős Problem 271

*Reference:* [erdosproblems.com/271](https://www.erdosproblems.com/271)
-/

open Filter Topology

namespace Erdos271

/--
Let $A(n)=\{a_0<a_1<\cdots\}$ be the sequence defined by $a_0=0$ and $a_1=n$.
For $k\geq 1$, define $a_{k+1}$ as the least positive integer such that
$\{a_0,\ldots,a_{k+1}\}$ contains no three-term arithmetic progression.

The problem asks: Can the $a_k$ be explicitly determined? How fast do they grow?

Known: $A(1)$ comprises integers with no digit 2 in base-3 expansion.
Odlyzko and Stanley identified similar characterizations for $A(3^k)$ and $A(2\cdot 3^k)$.
-/
axiom A (n : ℕ) : ℕ → ℕ

axiom A_zero (n : ℕ) : A n 0 = 0
axiom A_one (n : ℕ) : A n 1 = n
axiom A_increasing (n k : ℕ) : A n k < A n (k + 1)
axiom A_no_ap (n k : ℕ) : ∀ i j l : ℕ, i ≤ k → j ≤ k → l ≤ k → i < j → j < l →
    A n i + A n l ≠ 2 * A n j

/--
$A(1)$ comprises integers with no digit 2 in base-3 expansion.
-/
@[category research solved, AMS 11]
theorem erdos_271.A_one_characterization (k : ℕ) :
    A 1 k ∈ {n : ℕ | ∀ d : ℕ, d ∈ n.digits 3 → d ≠ 2} := by
  sorry

/--
Moy (2011): Upper bound $a_k \leq \frac{(k-1)(k+2)}{2}+n$.
-/
@[category research solved, AMS 11]
theorem erdos_271.moy_upper_bound (n k : ℕ) (hk : k ≥ 1) :
    A n k ≤ (k - 1) * (k + 2) / 2 + n := by
  sorry

/--
Open question: How fast do the sequences grow? Conjectured growth rates are
either $a_k \asymp k^{\log_2 3}$ or $a_k \asymp \frac{k^2}{\log k}$.
-/
@[category research open, AMS 11]
theorem erdos_271.growth_rate (n : ℕ) :
    (∃ C : ℝ, ∃ c : ℝ, C > 0 ∧ c > 0 ∧ ∀ k : ℕ, k ≥ 1 →
      c * (k : ℝ)^(Real.log 3 / Real.log 2) ≤ A n k ∧
      (A n k : ℝ) ≤ C * (k : ℝ)^(Real.log 3 / Real.log 2)) ∨
    (∃ C : ℝ, ∃ c : ℝ, C > 0 ∧ c > 0 ∧ ∀ k : ℕ, k ≥ 2 →
      c * (k : ℝ)^2 / Real.log (k : ℝ) ≤ A n k ∧
      (A n k : ℝ) ≤ C * (k : ℝ)^2 / Real.log (k : ℝ)) := by
  sorry

end Erdos271
