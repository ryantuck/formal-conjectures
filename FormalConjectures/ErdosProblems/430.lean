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
# Erdős Problem 430

Fix an integer n and define a decreasing sequence in [1,n) by:
- a₁ = n-1
- For k ≥ 2: aₖ is the greatest integer in [1, aₖ₋₁) such that all prime factors
  of aₖ are greater than n - aₖ

For sufficiently large n, must this sequence contain at least one composite number?

Related to Problem 385.

*Reference:* [erdosproblems.com/430](https://www.erdosproblems.com/430)
-/

open Filter Topology BigOperators

namespace Erdos430

/-- Erdős-Graham: Sequence contains composite for large n -/
@[category research open, AMS 11]
theorem erdos_430 :
    ∀ᶠ n : ℕ in atTop, ∃ seq : ℕ → ℕ,
      seq 0 = n - 1 ∧
      (∀ k : ℕ, seq k > seq (k + 1)) ∧
      (∀ k : ℕ, ∀ p : ℕ, p.Prime → p ∣ seq (k + 1) → n - seq (k + 1) < p) ∧
      (∃ k : ℕ, ¬(seq k).Prime ∧ seq k > 1) := by
  sorry

end Erdos430
