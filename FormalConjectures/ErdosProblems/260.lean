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
# Erdős Problem 260

*Reference:* [erdosproblems.com/260](https://www.erdosproblems.com/260)
-/

open Filter Topology

namespace Erdos260

/--
Let $a_1 < a_2 < \cdots$ be an increasing sequence such that $\frac{a_n}{n} \to \infty$.
Is the sum $\sum_n \frac{a_n}{2^{a_n}}$ irrational?

Erdős proved the sum is irrational under either:
- $a_{n+1} - a_n \to \infty$, or
- $a_n \gg n\sqrt{\log n \log \log n}$
-/
@[category research open, AMS 11]
theorem erdos_260 (a : ℕ → ℕ) (h_inc : ∀ n, a n < a (n + 1))
    (h_grow : Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) atTop atTop) :
    Irrational (∑' n : ℕ, (a n : ℝ) / (2 : ℝ)^(a n)) := by
  sorry

/--
Erdős proved irrationality when $a_{n+1} - a_n \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_260.gap_condition (a : ℕ → ℕ) (h_inc : ∀ n, a n < a (n + 1))
    (h_gap : Tendsto (fun n : ℕ => (a (n + 1) - a n : ℤ)) atTop atTop) :
    Irrational (∑' n : ℕ, (a n : ℝ) / (2 : ℝ)^(a n)) := by
  sorry

/--
Erdős proved irrationality when $a_n \gg n\sqrt{\log n \log \log n}$.
-/
@[category research solved, AMS 11]
theorem erdos_260.strong_growth (a : ℕ → ℕ) (h_inc : ∀ n, a n < a (n + 1))
    (h_strong : ∃ C > 0, ∀ n : ℕ, n ≥ 2 →
      (a n : ℝ) ≥ C * (n : ℝ) * Real.sqrt (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)))) :
    Irrational (∑' n : ℕ, (a n : ℝ) / (2 : ℝ)^(a n)) := by
  sorry

end Erdos260
