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
# Erdős Problem 34

*Reference:* [erdosproblems.com/34](https://www.erdosproblems.com/34)
-/

namespace Erdos34

open scoped BigOperators

/--
For a permutation `π` of `{0, ..., n-1}`, `S(π)` is the number of distinct consecutive sums
of the values `π(i) + 1` (to map to `{1, ..., n}`).
-/
def distinctConsecutiveSums (n : ℕ) (π : Equiv.Perm (Fin n)) : ℕ :=
  Finset.card (Finset.image (fun p : Fin n × Fin n ↦ ∑ i ∈ Finset.Icc (min p.1 p.2) (max p.1 p.2), ((π i) : ℕ) + 1) Finset.univ)

/--
Is it true that $S(\pi) = o(n^2)$ for all $\pi \in S_n$?

The answer is no. Konieczny [Ko15] showed that for a random permutation $S(\pi) \sim \frac{1+e^{-2}}{4}n^2$.

[Ko15] J. Konieczny, _On the number of distinct sums of consecutive terms of a permutation_,
arXiv:1502.00222 (2015).
-/
@[category research solved, AMS 11]
theorem erdos_34 : answer(False) ↔
    (fun n ↦ ((Finset.univ.sup (distinctConsecutiveSums n) : ℕ) : ℝ)) =o[Filter.atTop] (fun n ↦ (n : ℝ) ^ 2) := by
  sorry

end Erdos34
