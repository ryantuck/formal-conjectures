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
# Erdős Problem 202

*Reference:* [erdosproblems.com/202](https://www.erdosproblems.com/202)
-/

open Filter
open scoped Topology Real Pointwise

namespace Erdos202

/--
The maximum size of a set of disjoint congruence classes with distinct moduli up to $N$.
-/
noncomputable def f (N : ℕ) : ℕ :=
  sSup { r | ∃ (n : Fin r → ℕ) (a : Fin r → ℤ),
    (∀ i j, i < j → n i < n j) ∧
    (∀ i, 0 < n i ∧ n i ≤ N) ∧
    (∀ i j, i ≠ j → Disjoint ({a i} + Ideal.span {(n i : ℤ)} : Set ℤ) ({a j} + Ideal.span {(n j : ℤ)} : Set ℤ)) }

/--
The conjecture of de la Bretèche, Ford, and Vandehey [BFV13] is that
$f(N) = N / L(N)^{1+o(1)}$ where $L(N) = \exp(\sqrt{\log N \log \log N})$.

[BFV13] de la Bretèche, R., Ford, K., and Vandehey, J., _On the number of disjoint
congruence classes_, arXiv:1308.0994 (2013).
-/
@[category research open, AMS 11]
theorem erdos_202 :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
      (f N : ℝ) > N / (Real.exp (Real.sqrt (Real.log N * Real.log (Real.log N)))) ^ (1 + ε) ∧
      (f N : ℝ) < N / (Real.exp (Real.sqrt (Real.log N * Real.log (Real.log N)))) ^ (1 - ε) := by
  sorry

end Erdos202
