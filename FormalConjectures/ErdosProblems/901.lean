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
# Erdős Problem 901

Minimum edges in n-uniform 3-chromatic hypergraph.

OPEN

*Reference:* [erdosproblems.com/901](https://www.erdosproblems.com/901)
-/

open Finset

open scoped Topology Real

namespace Erdos901

variable {α : Type*}

/-- Chromatic number of hypergraph (minimum colors needed) -/
noncomputable def chromaticNumber (H : Finset (Finset α)) : ℕ := sorry

/-- n-uniform hypergraph (all edges have size n) -/
def IsUniform (H : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ e ∈ H, e.card = n

/-- m(n): minimum edges in n-uniform 3-chromatic hypergraph -/
noncomputable def m (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ (α : Type) (H : Finset (Finset α)),
    IsUniform H n ∧ H.card = k ∧ chromaticNumber H = 3}

/-- Known exact values -/
@[category research solved, AMS 5]
theorem exact_values : m 2 = 3 ∧ m 3 = 7 ∧ m 4 = 23 := by
  sorry

/-- Erdős bounds: 2ⁿ ≪ m(n) ≪ n²2ⁿ -/
@[category research solved, AMS 5]
theorem erdos_bounds :
    (∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      C₁ * (2 : ℝ) ^ n ≤ m n ∧ (m n : ℝ) ≤ C₂ * (n : ℝ) ^ 2 * (2 : ℝ) ^ n) := by
  sorry

/-- Radhakrishnan-Srinivasan lower bound: m(n) ≫ √(n/log n)·2ⁿ -/
@[category research solved, AMS 5]
theorem radhakrishnan_srinivasan :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (m n : ℝ) ≥ C * Real.sqrt (n / Real.log n) * (2 : ℝ) ^ n := by
  sorry

/-- Erdős-Lovász conjecture: m(n) ≈ n·2ⁿ -/
@[category research open, AMS 5]
theorem erdos_lovasz_conjecture :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ < C₂ ∧ ∀ n : ℕ, n ≥ 1 →
      C₁ * n * (2 : ℝ) ^ n ≤ (m n : ℝ) ∧ (m n : ℝ) ≤ C₂ * n * (2 : ℝ) ^ n := by
  sorry

end Erdos901
