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
# Erdős Problem 990

Polynomial root argument distribution.

OPEN

*Reference:* [erdosproblems.com/990](https://www.erdosproblems.com/990)
-/

open Finset Filter Polynomial

open scoped Topology Real

namespace Erdos990

/-- Polynomial root argument equidistribution -/
@[category research open, AMS 41]
theorem polynomial_root_distribution (answer : Prop) :
    answer ↔ ∀ (P : ℂ[X]) (n M : ℕ),
      let roots := P.roots.toFinset
      let nonzero_coeffs := {i : ℕ | P.coeff i ≠ 0}.ncard
      ∀ (I : Set ℝ) (μ : ℝ), I ⊆ Set.Icc 0 (2 * Real.pi) →
        |{z : ℂ | z ∈ roots ∧ Complex.arg z ∈ I}.ncard -
          (roots.card : ℝ) * (μ / (2 * Real.pi))| ≤
        Real.sqrt (nonzero_coeffs * Real.log M) := by
  sorry

end Erdos990
