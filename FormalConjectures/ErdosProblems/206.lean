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
# Erdős Problem 206

*Reference:* [erdosproblems.com/206](https://www.erdosproblems.com/206)
-/

open Filter
open scoped Topology Real

namespace Erdos206

/--
The maximal sum of $n$ distinct unit fractions which is strictly less than $x$.
-/
noncomputable def R (n : ℕ) (x : ℝ) : ℝ :=
  sSup { (∑ i ∈ S, (1 / i : ℝ)) | (S : Finset ℕ) (_ : S.card = n) (_ : ∀ i ∈ S, 0 < i) (_ : ∑ i ∈ S, (1 / i : ℝ) < x) }

/--
A set of $n$ distinct unit fractions $S$ is the "best underapproximation" if its sum is $R_n(x)$.
Note that such a set is unique for almost all $x$.
-/
def IsBestUnderapproximation (S : Finset ℕ) (n : ℕ) (x : ℝ) : Prop :=
  S.card = n ∧ (∀ i ∈ S, 0 < i) ∧ ∑ i ∈ S, (1 / i : ℝ) = R n x

/--
Is it true that for almost all $x$, for sufficiently large $n$, the best underapproximation
is constructed greedily?
-/
@[category research solved, AMS 11]
theorem erdos_206 :
    answer(False) ↔ ∀ᵐ x ∂MeasureTheory.volume, 0 < x → ∀ᶠ n in atTop,
      ∃ (S : Finset ℕ) (m : ℕ),
        IsBestUnderapproximation S n x ∧
        IsBestUnderapproximation (insert m S) (n + 1) x ∧
        m ∉ S ∧
        (∀ k ∉ S, 0 < k → (∑ i ∈ S, (1 / i : ℝ)) + 1 / k < x → 1 / k ≤ 1 / m) := by
  sorry

/--
Kovač [Ko24b] proved that the set of $x$ for which the property holds has Lebesgue measure zero.

[Ko24b] Kovač, V., _On the greedy property of the best underapproximations by sums of unit
fractions_, arXiv:2403.11921 (2024).
-/
@[category research solved, AMS 11]
theorem erdos_206.variants.measure_zero :
    MeasureTheory.volume { x : ℝ | 0 < x ∧ ∀ᶠ n in atTop,
      ∃ (S : Finset ℕ) (m : ℕ),
        IsBestUnderapproximation S n x ∧
        IsBestUnderapproximation (insert m S) (n + 1) x ∧
        m ∉ S ∧
        (∀ k ∉ S, 0 < k → (∑ i ∈ S, (1 / i : ℝ)) + 1 / k < x → 1 / k ≤ 1 / m) } = 0 := by
  sorry

end Erdos206
