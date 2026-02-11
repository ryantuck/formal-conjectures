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
# Erdős Problem 1133

Existence of polynomials with large bounds.

OPEN

*Reference:* [erdosproblems.com/1133](https://www.erdosproblems.com/1133)
-/

open Finset Filter

open scoped Real

namespace Erdos1133

/-- For any constant C > 0, there exists epsilon > 0 such that for sufficiently large n:
    given any points x_1, ..., x_n in [-1,1], one can find y_1, ..., y_n in [-1,1]
    such that any polynomial P of degree m < (1+epsilon)n satisfying P(x_i) = y_i
    for at least (1-epsilon)n indices must have max_{x in [-1,1]} |P(x)| > C. -/
@[category research open, AMS 41]
theorem polynomial_large_bounds (C : ℝ) (hC : 0 < C) :
    ∃ (ε : ℝ), 0 < ε ∧
      ∀ᶠ n in atTop, ∀ (x : Fin n → ℝ),
        (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) →
        ∃ (y : Fin n → ℝ), (∀ i, y i ∈ Set.Icc (-1 : ℝ) 1) ∧
          ∀ (P : Polynomial ℝ), P.natDegree < ⌈(1 + ε) * n⌉₊ →
            (↑{i : Fin n | P.eval (x i) = y i}.toFinset.card : ℝ) ≥ (1 - ε) * n →
            ⨆ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| > C := by
  sorry

end Erdos1133
