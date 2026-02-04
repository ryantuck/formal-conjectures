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
# Erdős Problem 272

*Reference:* [erdosproblems.com/272](https://www.erdosproblems.com/272)
-/

open Filter Topology

namespace Erdos272

/--
A set is an arithmetic progression if it has the form $\{a, a+d, a+2d, \ldots\}$ for some $a, d$.
-/
def IsArithmeticProgression (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ S = {n | ∃ k : ℕ, n = a + k * d}

/--
Let N ≥ 1. Find the largest t such that there exist $A_1,...,A_t \subseteq \{1,...,N\}$
where $A_i \cap A_j$ is a non-empty arithmetic progression for all $i \neq j$.

Szabo proved that maximal t equals $N^2/2 + O(N^{5/3}(\log N)^3)$.
-/
noncomputable def max_t (N : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ A : Fin t → Set ℕ,
    (∀ i, A i ⊆ Finset.range (N + 1)) ∧
    (∀ i j : Fin t, i ≠ j → (A i ∩ A j).Nonempty ∧ IsArithmeticProgression (A i ∩ A j))}

/--
Simonovits and Sós: $t \ll N^2$.
-/
@[category research solved, AMS 05]
theorem erdos_272.simonovits_sos_upper (N : ℕ) (hN : N ≥ 1) :
    ∃ C > 0, max_t N ≤ C * N^2 := by
  sorry

/--
Szabo: Maximal t equals $N^2/2 + O(N^{5/3}(\log N)^3)$.
-/
@[category research solved, AMS 05]
theorem erdos_272.szabo (N : ℕ) (hN : N ≥ 1) :
    ∃ C > 0, |(max_t N : ℝ) - (N : ℝ)^2 / 2| ≤ C * (N : ℝ)^(5/3) * (Real.log (N : ℝ))^3 := by
  sorry

/--
Szabo's construction: $t \geq \binom{N}{2} + \lfloor(N-1)/4\rfloor + 1$.
-/
@[category research solved, AMS 05]
theorem erdos_272.szabo_lower (N : ℕ) (hN : N ≥ 1) :
    max_t N ≥ Nat.choose N 2 + (N - 1) / 4 + 1 := by
  sorry

/--
Szabo conjectures the asymptotic is $t = \binom{N}{2} + O(N)$ with all sets sharing
a common element.
-/
@[category research open, AMS 05]
theorem erdos_272.szabo_conjecture (N : ℕ) (hN : N ≥ 1) :
    ∃ C > 0, |(max_t N : ℝ) - Nat.choose N 2| ≤ C * (N : ℝ) := by
  sorry

end Erdos272
