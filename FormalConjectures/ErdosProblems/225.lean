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
# Erdős Problem 225

*Reference:* [erdosproblems.com/225](https://www.erdosproblems.com/225)
-/

open Complex MeasureTheory

namespace Erdos225

/--
A trigonometric polynomial is a finite sum $f(\theta) = \sum_{k=0}^n c_k e^{ik\theta}$.
-/
def IsTrigonometricPolynomial (f : ℝ → ℂ) : Prop :=
  ∃ n : ℕ, ∃ c : Fin (n + 1) → ℂ, ∀ θ, f θ = ∑ k : Fin (n + 1), c k * Complex.exp (Complex.I * k * θ)

/--
All roots of a function are real.
-/
def HasAllRealRoots (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f z = 0 → z.im = 0

/--
Let $f(\theta) = \sum_{0\leq k\leq n}c_k e^{ik\theta}$ be a trigonometric polynomial
all of whose roots are real, such that $\max_{\theta\in [0,2\pi]}|f(\theta)|=1$.
Then $\int_0^{2\pi}|f(\theta)| d\theta \leq 4$.

This was solved independently by Kristiansen [Kr74] (for real coefficients)
and Saff and Sheil-Small [SaSh74] (for complex coefficients).

[Kr74] Kristiansen, G. K., _On a problem of Erdős and Halmos_.
  Det. Kon. Norske Vid. Selskabs Skrifter (1974), 1-6.

[SaSh74] Saff, E. B. and Sheil-Small, T., _Coefficient and integral mean estimates
  for algebraic and trigonometric polynomials with restricted zeros_.
  J. London Math. Soc. (1974), 16-22.
-/
@[category research solved, AMS 30]
theorem erdos_225 : ∀ f : ℝ → ℂ,
    IsTrigonometricPolynomial f →
    HasAllRealRoots (fun z ↦ f z.re) →
    (⨆ θ ∈ Set.Icc 0 (2 * Real.pi), ‖f θ‖) = 1 →
    ∫ θ in (0)..(2 * Real.pi), ‖f θ‖ ≤ 4 := by
  sorry

end Erdos225
