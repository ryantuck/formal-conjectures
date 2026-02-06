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
# Erdős Problem 653

For n points in ℝ², is the maximum number of distinct values R(x_i) can take ≥ (1-o(1))n?

OPEN

*Reference:* [erdosproblems.com/653](https://www.erdosproblems.com/653)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos653

/-- R(x_i): count of distinct distances from x_i to other points -/
noncomputable def R {n : ℕ} (points : Finset (Fin 2 → ℝ)) (i : Fin n) : ℕ := sorry

/-- g(n): max distinct values of R(x_i) -/
noncomputable def g (n : ℕ) : ℕ := sorry

/-- Is g(n) ≥ (1-o(1))n? -/
@[category research open, AMS 52]
theorem distinct_distance_counts (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      g n ≥ Nat.floor ((1 - ε) * n) := by
  sorry

end Erdos653
