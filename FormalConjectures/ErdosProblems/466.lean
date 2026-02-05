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
# Erdős Problem 466

Let N(X,δ) denote the maximum number of points P₁,...,Pₙ in a circle of radius X such
that ‖Pᵢ-Pⱼ‖ ≥ δ for all i < j. Is there some δ > 0 such that lim_{X→∞} N(X,δ) = ∞?

Graham: PROVED - N(X, 1/10) > (log X)/10.
Sárközy: For all sufficiently small δ > 0, N(X,δ) > X^(1/2-δ^(1/7)).

*Reference:* [erdosproblems.com/466](https://www.erdosproblems.com/466)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos466

/-- Distance to nearest integer -/
noncomputable def distInt (x : ℝ) : ℝ :=
  min (x - ⌊x⌋) (⌈x⌉ - x)

/-- N(X,δ) is the maximum packing number -/
noncomputable def N (X δ : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ pts : Fin n → ℝ, (∀ i, ‖pts i‖ ≤ X) ∧
    ∀ i j : Fin n, i ≠ j → distInt (pts i - pts j) ≥ δ}

/-- Graham: Logarithmic lower bound -/
@[category research solved, AMS 11]
theorem erdos_466_graham :
    Tendsto (fun X : ℝ => (N X (1/10) : ℝ)) atTop atTop := by
  sorry

/-- Sárközy: Power lower bound -/
@[category research solved, AMS 11]
theorem erdos_466_sarkozy :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ X : ℝ in atTop,
      (N X δ : ℝ) > X ^ ((1:ℝ)/2 - δ ^ ((1:ℝ)/7)) := by
  sorry

end Erdos466
