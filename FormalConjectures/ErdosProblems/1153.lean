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
# Erdős Problem 1153

Lagrange basis functions and subintervals.

OPEN

*Reference:* [erdosproblems.com/1153](https://www.erdosproblems.com/1153)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1153

/-- Lagrange basis polynomial -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ := sorry

/-- Sum of absolute values of Lagrange basis functions -/
noncomputable def Λ {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis nodes k x|

/-- Lagrange basis functions and subintervals -/
@[category research open, AMS 41]
theorem lagrange_basis_subintervals (answer : Prop) :
    answer ↔ ∀ (a b : ℝ), -1 ≤ a → a < b → b ≤ 1 →
      ∀ᶠ n : ℕ in atTop, ∃ (nodes : Fin n → ℝ),
        (∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1) ∧
        (∀ i j, i ≠ j → nodes i ≠ nodes j) ∧
        (⨆ x ∈ Set.Icc a b, Λ nodes x) > (2 / Real.pi - sorry) * Real.log n := by
  sorry

end Erdos1153
