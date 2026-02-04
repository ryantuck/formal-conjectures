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
# Erdős Problem 265

*Reference:* [erdosproblems.com/265](https://www.erdosproblems.com/265)
-/

open Filter Topology

namespace Erdos265

/--
Let $1 \leq a_1 < a_2 < \cdots$ be an increasing sequence of integers.
How fast can $a_n \to \infty$ grow if both $\sum(1/a_n)$ and $\sum(1/(a_n-1))$ are rational?

Known examples: $a_n = \binom{n}{2}$ (Cantor) and $a_n = n^3 + 6n^2 + 5n$ work.

Erdős conjectured: Such sequences can grow where $a_n^{1/n} \to \infty$,
but $a_n^{1/2^n} \to 1$ is necessary.

Kovač and Tao (2024): Sequences can grow doubly exponentially with $a_n^{1/\beta^n} \to \infty$
for some $\beta > 1$.
-/
@[category research open, AMS 11]
theorem erdos_265 : ∃ a : ℕ → ℕ, (∀ n, 1 ≤ a n ∧ a n < a (n + 1)) ∧
    (∃ q₁ q₂ : ℚ, (∑' n : ℕ, (1 : ℝ) / (a n : ℝ)) = q₁ ∧
      (∑' n : ℕ, (1 : ℝ) / ((a n : ℝ) - 1)) = q₂) ∧
    Tendsto (fun n : ℕ => (a n : ℝ)^((1 : ℝ) / (n : ℝ))) atTop atTop := by
  sorry

/--
Cantor's example: $a_n = \binom{n}{2} = n(n-1)/2$ satisfies both conditions.
-/
@[category research solved, AMS 11]
theorem erdos_265.cantor_example :
    let a := fun n : ℕ => n * (n - 1) / 2
    (∃ q₁ q₂ : ℚ, (∑' n : ℕ, (1 : ℝ) / (a (n + 2) : ℝ)) = q₁ ∧
      (∑' n : ℕ, (1 : ℝ) / ((a (n + 2) : ℝ) - 1)) = q₂) := by
  sorry

/--
Kovač and Tao (2024): There exist sequences growing doubly exponentially.
Specifically, sequences where $a_n^{1/\beta^n} \to \infty$ for some $\beta > 1$.
-/
@[category research solved, AMS 11]
theorem erdos_265.kovac_tao : ∃ a : ℕ → ℕ, ∃ β > 1,
    (∀ n, 1 ≤ a n ∧ a n < a (n + 1)) ∧
    (∃ q₁ q₂ : ℚ, (∑' n : ℕ, (1 : ℝ) / (a n : ℝ)) = q₁ ∧
      (∑' n : ℕ, (1 : ℝ) / ((a n : ℝ) - 1)) = q₂) ∧
    Tendsto (fun n : ℕ => (a n : ℝ)^((1 : ℝ) / β^n)) atTop atTop := by
  sorry

/--
Erdős's conjecture on the necessary condition: If both sums are rational,
then $a_n^{1/2^n} \to 1$ is necessary.
-/
@[category research open, AMS 11]
theorem erdos_265.necessary_condition (a : ℕ → ℕ)
    (h_inc : ∀ n, 1 ≤ a n ∧ a n < a (n + 1))
    (h_rat : ∃ q₁ q₂ : ℚ, (∑' n : ℕ, (1 : ℝ) / (a n : ℝ)) = q₁ ∧
      (∑' n : ℕ, (1 : ℝ) / ((a n : ℝ) - 1)) = q₂) :
    Tendsto (fun n : ℕ => (a n : ℝ)^((1 : ℝ) / (2 : ℝ)^n)) atTop (𝓝 1) := by
  sorry

end Erdos265
