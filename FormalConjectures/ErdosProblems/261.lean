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
# Erdős Problem 261

*Reference:* [erdosproblems.com/261](https://www.erdosproblems.com/261)
-/

open Filter Topology

namespace Erdos261

/--
Are there infinitely many values of n such that there exist t ≥ 2 and distinct integers
$a_1,...,a_t \geq 1$ satisfying: $n/2^n = \sum_{k=1}^t a_k/2^{a_k}$?

This was answered affirmatively by Cusick.
-/
@[category research solved, AMS 11]
theorem erdos_261.infinitely_many :
    Set.Infinite {n : ℕ | ∃ (t : ℕ) (ht : t ≥ 2) (a : Fin t → ℕ),
      (∀ i, a i ≥ 1) ∧ (∀ i j, i ≠ j → a i ≠ a j) ∧
      (n : ℝ) / (2 : ℝ)^n = ∑ i : Fin t, (a i : ℝ) / (2 : ℝ)^(a i)} := by
  sorry

/--
Borwein and Loring (1990): For n = 2^(m+1) - m - 2, the equation holds.
-/
@[category research solved, AMS 11]
theorem erdos_261.borwein_loring (m : ℕ) :
    let n := 2^(m + 1) - m - 2
    ∃ (t : ℕ) (ht : t ≥ 2) (a : Fin t → ℕ),
      (∀ i, a i ≥ 1) ∧ (∀ i j, i ≠ j → a i ≠ a j) ∧
      (n : ℝ) / (2 : ℝ)^n = ∑ i : Fin t, (a i : ℝ) / (2 : ℝ)^(a i) := by
  sorry

/--
Does there exist a rational x such that $x = \sum a_k/2^{a_k}$ has at least $2^{\aleph_0}$
solutions (i.e., continuum many representations)?
-/
@[category research open, AMS 11]
theorem erdos_261.continuum_representations :
    ∃ (x : ℚ), ∃ f : Set (ℕ → ℕ),
      f.Infinite ∧
      (∀ a ∈ f, (∀ i j, i < j → a i < a j) ∧
        (x : ℝ) = ∑' i : ℕ, if a i = 0 then 0 else (a i : ℝ) / (2 : ℝ)^(a i)) := by
  sorry

end Erdos261
