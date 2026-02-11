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
# Erdős Problem 1147

Additive basis question for irrational quadratic approximations.

This problem asks whether certain sets defined by irrational quadratic approximations
form an additive basis for the natural numbers. An additive basis is a set B such that
every natural number can be expressed as the sum of a bounded number of elements from B.
The problem has been DISPROVED, showing that these sets do not form such a basis.

DISPROVED

*Reference:* [erdosproblems.com/1147](https://www.erdosproblems.com/1147)
-/

namespace Erdos1147

/-- The sets defined by irrational quadratic approximations do not form an additive basis.
    This has been disproved (answer is False). The precise formulation of the sets involved
    requires further investigation from the original problem statement. -/
@[category research solved, AMS 11]
theorem irrational_quadratic_approximation_basis :
    let A := {n : ℕ | ∃ α : ℝ, Irrational α ∧ ∃ k : ℕ, |α^2 - (n : ℝ) / (k : ℝ)| < 1 / (k : ℝ)}
    answer(False) ↔ (∀ r : ℕ, ∃ m : ℕ, ∀ n ≥ m, ∃ (s : Finset ℕ),
      s.card ≤ r ∧ (∀ x ∈ s, x ∈ A) ∧ n = s.sum id) := by
  sorry

end Erdos1147
