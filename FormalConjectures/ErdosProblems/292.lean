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
# Erdős Problem 292

*Reference:* [erdosproblems.com/292](https://www.erdosproblems.com/292)
-/

open Filter Topology

namespace Erdos292

/--
Let A be the set of natural numbers n for which there exist integers $1 \leq m_1 < \cdots < m_k = n$
satisfying $\sum(1/m_i) = 1$.

Does A have density 1?

Martin (2000) proved the answer is affirmative.
-/
def A : Set ℕ :=
  {n : ℕ | ∃ (k : ℕ) (m : Fin k → ℕ),
    (∀ i, m i ≥ 1) ∧
    (∀ i j, i < j → m i < m j) ∧
    (∃ i, m i = n) ∧
    (1 : ℝ) = ∑ i : Fin k, (1 : ℝ) / (m i : ℝ)}

/--
Martin (2000): A has density 1. More precisely, for large x:
$|B ∩ [1,x]|/x \approx (\log \log x)/(\log x)$ where B = ℕ \ A.
-/
@[category research solved, AMS 11]
theorem erdos_292 :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∃ count : ℕ,
      (count : ℝ) ≥ (1 - ε) * (N : ℝ) := by
  sorry

/--
Straus: A is closed under multiplication.
-/
@[category research solved, AMS 11]
theorem erdos_292.straus_multiplicative (n m : ℕ) (hn : n ∈ A) (hm : m ∈ A) :
    n * m ∈ A := by
  sorry

/--
A excludes all prime powers.
-/
@[category research solved, AMS 11]
theorem erdos_292.no_prime_powers (p : ℕ) (k : ℕ) (hp : Nat.Prime p) (hk : k ≥ 1) :
    p^k ∉ A := by
  sorry

end Erdos292
