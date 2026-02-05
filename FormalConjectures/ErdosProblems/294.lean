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
# Erdős Problem 294

*Reference:* [erdosproblems.com/294](https://www.erdosproblems.com/294)
-/

open Finset

namespace Erdos294

/--
The least integer $t$ such that there is no solution to $1=\sum_{i=1}^k\frac{1}{n_i}$
with $t=n_1<\cdots <n_k\leq N$.
-/
def t (N : ℕ) : ℕ := N

/--
Let $N \geq 1$ and let $t(N)$ be the least integer $t$ such that there is no solution to
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$
with $t=n_1<\cdots <n_k\leq N$. Estimate $t(N)$.

Erdős and Graham established an upper bound: $t(N)\ll\frac{N}{\log N}$.

Liu and Sawhney (2024) determined the asymptotic behavior up to $(\log\log N)^{O(1)}$ factors:
$$\frac{N}{(\log N)(\log\log N)^3(\log\log\log N)^{O(1)}}\ll t(N) \ll \frac{N}{\log N}$$
-/
@[category research solved, AMS 11]
theorem erdos_294 : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
    let logN := Real.log (N : ℝ)
    let loglogN := Real.log logN
    let logloglogN := Real.log loglogN
    (c * N / (logN * loglogN^3 * logloglogN) ≤ (t N : ℝ)) ∧
    ((t N : ℝ) ≤ C * N / logN) := by
  sorry

end Erdos294
