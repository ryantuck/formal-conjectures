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
# Erdős Problem 286

*Reference:* [erdosproblems.com/286](https://www.erdosproblems.com/286)
-/

open Filter Topology

namespace Erdos286

/--
Let k ≥ 2. Does there exist an interval I of width $(e-1+o(1))k$ and integers
$n_1 < \cdots < n_k \in I$ such that: $1 = \frac{1}{n_1} + \cdots + \frac{1}{n_k}$?

Croot [Cr01] proved the answer is affirmative.
-/
@[category research solved, AMS 11]
theorem erdos_286 (k : ℕ) (hk : k ≥ 2) :
    ∃ I : Set ℕ, ∃ a b : ℕ, I = Set.Icc a b ∧
      ((b - a : ℝ) ≤ (Real.exp 1 - 1 + 1) * (k : ℝ)) ∧
      ∃ (n : Fin k → ℕ), (∀ i, n i ∈ I) ∧
        (∀ i j, i < j → n i < n j) ∧
        (1 : ℝ) = ∑ i : Fin k, (1 : ℝ) / (n i : ℝ) := by
  sorry

end Erdos286
