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
# Erdős Problem 54

*Reference:* [erdosproblems.com/54](https://www.erdosproblems.com/54)
-/

namespace Erdos54

open scoped BigOperators

/--
A set of integers $A$ is Ramsey $r$-complete if, whenever $A$ is $r$-coloured, all sufficiently
large integers can be written as a monochromatic sum of elements of $A$.
-/ 
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ (c : ℕ → Fin r), ∃ (n₀ : ℕ), ∀ (n : ℕ), n₀ ≤ n →
    ∃ (S : Finset ℕ), ↑S ⊆ A ∧ (∃ i, ∀ s ∈ S, c s = i) ∧ ∑ s ∈ S, s = n

/--
Burr and Erdős [BuEr85] showed that there exists a constant $c>0$ such that if $A$ is Ramsey
$2$-complete then
$$\lvert A\cap \{1,\ldots,N\}\rvert \geq c(\log N)^2$$
for all large $N$.

[BuEr85] S. A. Burr and P. Erdős, _Subsets of integers with a coloring property_,
Combinatorica (1985), 13–27.
-/ 
@[category research solved, AMS 11]
theorem erdos_54_lower_bound : ∃ (c : ℝ), 0 < c ∧ ∀ (A : Set ℕ), IsRamseyComplete A 2 →
    ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    (Set.ncard (A ∩ Finset.Icc 1 N) : ℝ) ≥ c * (Real.log N) ^ 2 := by
  sorry

/--
Conlon, Fox, and Pham [CFP21] showed that there exists a Ramsey $2$-complete $A$ such that
$$\lvert A\cap \{1,\ldots,N\}\rvert \ll (\log N)^2$$
for all large $N$.

[CFP21] D. Conlon, J. Fox, and H. T. Pham, _A solution to the Ramsey complete subset problem_,
arXiv:2111.05436 (2021).
-/ 
@[category research solved, AMS 11]
theorem erdos_54_upper_bound : ∃ (A : Set ℕ), IsRamseyComplete A 2 ∧
    ∃ (C : ℝ), ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    (Set.ncard (A ∩ Finset.Icc 1 N) : ℝ) ≤ C * (Real.log N) ^ 2 := by
  sorry

end Erdos54
