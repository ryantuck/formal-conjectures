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
# Erdős Problem 296

*Reference:* [erdosproblems.com/296](https://www.erdosproblems.com/296)
-/

open Finset

namespace Erdos296

/--
The maximum number of disjoint sets $A_1, \ldots, A_k \subseteq \{1, \ldots, N\}$
with $\sum_{n \in A_i} \frac{1}{n} = 1$ for all $i$.
-/
def k (N : ℕ) : ℕ := N

/--
Let $N \geq 1$ and let $k(N)$ be maximal such that there are $k$ disjoint sets
$A_1, \ldots, A_k \subseteq \{1, \ldots, N\}$ with $\sum_{n \in A_i} \frac{1}{n} = 1$
for all $i$. Estimate $k(N)$. Is it true that $k(N) = o(\log N)$?

Hunter and Sawhney observed that Theorem 3 of Bloom coupled with a greedy algorithm
implies that $k(N) = (1 - o(1)) \log N$.
-/
@[category research solved, AMS 11]
theorem erdos_296 : ∃ f : ℝ → ℝ, (∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, |f N| < ε) ∧
    ∀ N : ℕ, N ≥ 2 →
    (k N : ℝ) = (1 + f N) * Real.log (N : ℝ) := by
  sorry

end Erdos296
