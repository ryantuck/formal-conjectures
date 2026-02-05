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
# Erdős Problem 404

For integers $a \geq 1$ and primes $p$, determine which pairs have finite upper bound on $k$
such that $p^k \mid (a_1! + \cdots + a_n!)$ with $a = a_1 < \cdots < a_n$.

Let f(a,p) be the greatest such k. Does there exist prime p and sequence $a_1 < a_2 < \cdots$
where the highest power of p dividing $\sum_{i \leq k} a_i!$ tends to infinity?

Lin: f(2,2) ≤ 254.

*Reference:* [erdosproblems.com/404](https://www.erdosproblems.com/404)
-/

open Filter Topology BigOperators

namespace Erdos404

/-- f(a,p) is the maximum k such that p^k divides some factorial sum starting with a -/
noncomputable def f (a p : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset ℕ, a ∈ S ∧ p.Prime ∧
    p^k ∣ (S.sum Nat.factorial)}

/-- Lin: f(2,2) ≤ 254 -/
@[category research open, AMS 11]
theorem erdos_404_lin : f 2 2 ≤ 254 := by
  sorry

end Erdos404
