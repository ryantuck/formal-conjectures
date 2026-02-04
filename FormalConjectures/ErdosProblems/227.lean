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
# Erdős Problem 227

*Reference:* [erdosproblems.com/227](https://www.erdosproblems.com/227)
-/

open Complex Filter Topology

namespace Erdos227

/--
The ratio of the maximum coefficient magnitude to the maximum function value on a circle.
-/
noncomputable def coefficientRatio (f : ℂ → ℂ) (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  (⨆ n : ℕ, Complex.norm (a n * r^n)) / (⨆ z : ℂ, if Complex.norm z = r then Complex.norm (f z) else 0)

/--
Let $f=\sum_{n=0}^\infty a_nz^n$ be an entire function which is not a polynomial.
Is it true that if $\lim_{r\to \infty} \frac{\max_n|a_nr^n|}{\max_{|z|=r}|f(z)|}$ exists
then it must be $0$?

This was disproved by Clunie and Hayman [ClHa64], who showed that the limit
can take any value in $[0,1/2]$.

[ClHa64] Clunie, J. and Hayman, W. K., _The maximum term of a power series_.
  J. d'Analyse Math. (1964), 439-505.
-/
@[category research solved, AMS 30]
theorem erdos_227 : ¬ ∀ f : ℂ → ℂ, ∀ a : ℕ → ℂ,
    Differentiable ℂ f →
    (∀ z, f z = ∑' n : ℕ, a n * z^n) →
    (¬ ∃ N : ℕ, ∀ n > N, a n = 0) →
    (∃ L, Tendsto (fun r ↦ coefficientRatio f a r) atTop (𝓝 L)) →
    (∃ L, Tendsto (fun r ↦ coefficientRatio f a r) atTop (𝓝 L) ∧ L = 0) := by
  sorry

/--
Clunie proved this if $a_n \geq 0$ for all $n$.
-/
@[category research solved, AMS 30]
theorem erdos_227.clunie_positive : ∀ f : ℂ → ℂ, ∀ a : ℕ → ℝ,
    Differentiable ℂ f →
    (∀ z, f z = ∑' n : ℕ, (a n : ℂ) * z^n) →
    (∀ n, 0 ≤ a n) →
    (¬ ∃ N : ℕ, ∀ n > N, a n = 0) →
    (∃ L, Tendsto (fun r ↦ coefficientRatio f (fun n ↦ a n) r) atTop (𝓝 L)) →
    (∃ L, Tendsto (fun r ↦ coefficientRatio f (fun n ↦ a n) r) atTop (𝓝 L) ∧ L = 0) := by
  sorry

end Erdos227
