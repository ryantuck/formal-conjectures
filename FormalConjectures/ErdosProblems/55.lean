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
# Erdős Problem 55

*Reference:* [erdosproblems.com/55](https://www.erdosproblems.com/55)
-/

namespace Erdos55

open scoped BigOperators

/--
A set of integers $A$ is Ramsey $r$-complete if, whenever $A$ is $r$-coloured, all sufficiently
large integers can be written as a monochromatic sum of elements of $A$.
-/ 
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop := 
  ∀ (c : ℕ → Fin r), ∃ (n₀ : ℕ), ∀ (n : ℕ), n₀ ≤ n →
    ∃ (S : Finset ℕ), ↑S ⊆ A ∧ (∃ i, ∀ s ∈ S, c s = i) ∧ ∑ s ∈ S, s = n

/--
Conlon, Fox, and Pham [CFP21] constructed for every $r \ge 2$ an $r$-Ramsey complete $A$ 
such that for all large $N$
$$\lvert A\cap \{1,\ldots,N\rvert \ll r(\log N)^2,$$ 
and showed that this is best possible.

[CFP21] D. Conlon, J. Fox, and H. T. Pham, _A solution to the Ramsey complete subset problem_,
arXiv:2111.05436 (2021).
-/
@[category research solved, AMS 11]
theorem erdos_55 : answer(True) ↔ ∀ r : ℕ, 2 ≤ r →
    (∃ A, IsRamseyComplete A r ∧
      ∃ C, ∃ N₀, ∀ N, N₀ ≤ N →
      ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * (r : ℝ) * (Real.log N) ^ 2) ∧
    ∃ c, 0 < c ∧ ∀ A, IsRamseyComplete A r →
      ∃ N₀, ∀ N, N₀ ≤ N →
      ((A ∩ Set.Icc 1 N).ncard : ℝ) ≥ c * (r : ℝ) * (Real.log N) ^ 2 := by
  sorry

end Erdos55