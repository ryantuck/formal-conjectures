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
# Erdős Problem 290

*Reference:* [erdosproblems.com/290](https://www.erdosproblems.com/290)
-/

open Filter Topology

namespace Erdos290

/--
Let $a \geq 1$. Must there exist some $b > a$ such that:
$$\sum_{a \leq n \leq b}\frac{1}{n}=\frac{r_1}{s_1} \text{ and }
  \sum_{a \leq n \leq b+1}\frac{1}{n}=\frac{r_2}{s_2}$$
with $(r_i,s_i)=1$ and $s_2 < s_1$?

Van Doorn (2024) resolved this affirmatively, proving $b(a)$ always exists with $b(a) \ll a$.
-/
noncomputable def harmonic_sum (a b : ℕ) : ℚ :=
  (Finset.Ico a (b + 1)).sum (fun n : ℕ => (1 : ℚ) / n)

/--
Van Doorn (2024): For all $a \geq 1$, there exists $b > a$ such that the denominator
of the reduced fraction for $\sum_{a \leq n \leq b+1} 1/n$ is less than the denominator
for $\sum_{a \leq n \leq b} 1/n$.
-/
@[category research solved, AMS 11]
theorem erdos_290 (a : ℕ) (ha : a ≥ 1) :
    ∃ b : ℕ, b > a ∧ (harmonic_sum a (b + 1)).den < (harmonic_sum a b).den := by
  sorry

/--
Van Doorn: $b(a) < 4.374a$ for all $a > 1$.
-/
@[category research solved, AMS 11]
theorem erdos_290.van_doorn_upper (a : ℕ) (ha : a > 1) :
    ∃ b : ℕ, b > a ∧ b < (4.374 * a : ℝ) ∧
      (harmonic_sum a (b + 1)).den < (harmonic_sum a b).den := by
  sorry

/--
Van Doorn: $b(a) > a + 0.54\log a$ for large $a$.
-/
@[category research solved, AMS 11]
theorem erdos_290.van_doorn_lower :
    ∃ A : ℕ, ∀ a ≥ A, ∀ b : ℕ,
      (harmonic_sum a (b + 1)).den < (harmonic_sum a b).den →
        (b : ℝ) > (a : ℝ) + 0.54 * Real.log (a : ℝ) := by
  sorry

end Erdos290
