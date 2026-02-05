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
# Erdős Problem 360

Let f(n) be the minimum number of classes needed to partition {1,...,n-1} such that n
cannot be expressed as a sum of distinct elements from any single class.
How fast does f(n) grow?

SOLVED:
- Alon-Erdős (1996): f(n) = n^(1/3+o(1)) with bounds
  n^(1/3)/(log n)^(4/3) ≪ f(n) ≪ n^(1/3)/(log n)^(1/3) (log log n)^(1/3)
- Vu (2007): Improved lower bound to f(n) ≫ n^(1/3)/log n
- Conlon-Fox-Pham (2021): Determined asymptotic growth
  f(n) ≍ n^(1/3)(n/φ(n)) / ((log n)^(1/3)(log log n)^(2/3))

*Reference:* [erdosproblems.com/360](https://www.erdosproblems.com/360)
-/

open Filter Topology BigOperators Real

namespace Erdos360

/-- f(n) is the minimum number of classes in a partition of {1,...,n-1} such that
    n is not a sum of distinct elements from any single class -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ P : Fin k → Set ℕ,
    (∀ i : Fin k, P i ⊆ Finset.range n) ∧
    (∀ i j : Fin k, i ≠ j → Disjoint (P i) (P j)) ∧
    (⋃ i : Fin k, P i) = Finset.range n ∧
    (∀ i : Fin k, ¬∃ S : Finset ℕ, (S : Set ℕ) ⊆ P i ∧ S.sum id = n)}

/-- Alon-Erdős: Lower bound -/
@[category research solved, AMS 11]
theorem erdos_360_alon_erdos_lower :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≥ c * (n : ℝ)^(1/3 : ℝ) / (Real.log n)^(4/3 : ℝ) := by
  sorry

/-- Alon-Erdős: Upper bound -/
@[category research solved, AMS 11]
theorem erdos_360_alon_erdos_upper :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop,
      (f n : ℝ) ≤ c * (n : ℝ)^(1/3 : ℝ) * (Real.log (Real.log n))^(1/3 : ℝ) / (Real.log n)^(1/3 : ℝ) := by
  sorry

/-- Vu: Improved lower bound -/
@[category research solved, AMS 11]
theorem erdos_360_vu :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≥ c * (n : ℝ)^(1/3 : ℝ) / Real.log n := by
  sorry

/-- Conlon-Fox-Pham: Asymptotic formula -/
@[category research solved, AMS 11]
theorem erdos_360_cfp :
    Tendsto (fun n => (f n : ℝ) * (Real.log n)^(1/3 : ℝ) * (Real.log (Real.log n))^(2/3 : ℝ) /
      ((n : ℝ)^(1/3 : ℝ) * ((n : ℝ) / Nat.totient n))) atTop (𝓝 1) := by
  sorry

end Erdos360
