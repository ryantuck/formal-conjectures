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
# Erdős Problem 1109

Squarefree sumsets.

OPEN

*Reference:* [erdosproblems.com/1109](https://www.erdosproblems.com/1109)
-/

open Finset

open scoped Real

namespace Erdos1109

/-- f(N) = the size of the largest A ⊆ {1,...,N} with A+A squarefree. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = k ∧
    ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)}

/-- Lower bound: f(N) >> (log N)^2 * log(log N) (Konyagin). -/
@[category research open, AMS 11]
theorem squarefree_sumsets_lower :
    ∃ c > 0, ∀ᶠ N in Filter.atTop,
      c * (Real.log N)^2 * Real.log (Real.log N) ≤ (f N : ℝ) := by
  sorry

/-- Upper bound: f(N) << N^{11/15 + o(1)} (Konyagin). -/
@[category research open, AMS 11]
theorem squarefree_sumsets_upper :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ N in Filter.atTop,
      (f N : ℝ) ≤ C * (N : ℝ) ^ (11/15 + ε) := by
  sorry

/-- Open: Is f(N) ≤ N^{o(1)}? -/
@[category research open, AMS 11]
theorem squarefree_sumsets_subpolynomial :
    answer(sorry) ↔ ∀ ε > 0, ∃ C > 0, ∀ᶠ N in Filter.atTop,
      (f N : ℝ) ≤ C * (N : ℝ) ^ ε := by
  sorry

end Erdos1109
