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
# Erdős Problem 1151

Lagrange interpolation and limit points.

OPEN

*Reference:* [erdosproblems.com/1151](https://www.erdosproblems.com/1151)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1151

/-- Chebyshev nodes in [-1,1] -/
noncomputable def chebyshevNodes (n : ℕ) (i : Fin n) : ℝ :=
  Real.cos (Real.pi * (2 * (i : ℝ) + 1) / (2 * n))

/-- Lagrange interpolation operator -/
noncomputable def lagrangeInterp {n : ℕ} (nodes : Fin n → ℝ) (f : ℝ → ℝ) : ℝ → ℝ := sorry

/-- Lagrange interpolation and limit points -/
@[category research open, AMS 41]
theorem lagrange_interpolation_limit_points :
    ∀ (A : Set ℝ), IsClosed A → A ⊆ Set.Icc (-1 : ℝ) 1 →
      ∃ (f : ℝ → ℝ), Continuous f ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1,
          {y | ∃ (seq : ℕ → ℕ), Tendsto seq atTop atTop ∧
            Tendsto (fun n => lagrangeInterp (chebyshevNodes (seq n)) f x) atTop (𝓝 y)} = A) := by
  sorry

end Erdos1151
