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
# Erdős Problem 465

Let N(X,δ) denote the maximum number of points P₁,...,Pₙ in a circle of radius X such
that ‖Pᵢ-Pⱼ‖ ≥ δ for all i < j, where ‖x‖ is the distance to the nearest integer.

Questions:
1. Is N(X,δ) = o(X) for any 0 < δ < 1/2?
2. Is N(X,δ) < X^(1/2+o(1)) for any fixed δ > 0?

Sárközy (1976): PROVED question 1 - N(X,δ) ≪ δ⁻³X/log log X.
Konyagin (2001): N(X,δ) ≪_δ X^(1/2).

*Reference:* [erdosproblems.com/465](https://www.erdosproblems.com/465)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos465

/-- Distance to nearest integer -/
noncomputable def distInt (x : ℝ) : ℝ :=
  min (x - ⌊x⌋) (⌈x⌉ - x)

/-- N(X,δ) is the maximum packing number -/
noncomputable def N (X δ : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ pts : Fin n → ℝ, (∀ i, ‖pts i‖ ≤ X) ∧
    ∀ i j : Fin n, i ≠ j → distInt (pts i - pts j) ≥ δ}

/-- Sárközy: N(X,δ) = o(X) -/
@[category research solved, AMS 11]
theorem erdos_465_sarkozy :
    ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      Tendsto (fun X : ℝ => (N X δ : ℝ) / X) atTop (𝓝 0) := by
  sorry

/-- Konyagin: Square root bound -/
@[category research solved, AMS 11]
theorem erdos_465_konyagin :
    ∀ δ : ℝ, δ > 0 → ∃ C : ℝ, C > 0 ∧ ∀ X : ℝ, X ≥ 1 →
      (N X δ : ℝ) ≤ C * X ^ ((1:ℝ)/2) := by
  sorry

end Erdos465
