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
# Erdős Problem 262

*Reference:* [erdosproblems.com/262](https://www.erdosproblems.com/262)
-/

open Filter Topology

namespace Erdos262

/--
A sequence $a_1 < a_2 < \cdots$ is an "irrationality sequence" if for all sequences $t_n$
with $t_n \geq 1$, the sum $\sum_{n=1}^{\infty} \frac{1}{t_n a_n}$ is irrational.

Suppose $a_1 < a_2 < \cdots$ is a sequence of integers such that for all integer sequences
$t_n$ with $t_n \geq 1$ the sum is irrational. How slowly can $a_n$ grow?

Hančl (1991) proved that such sequences must satisfy:
$\limsup_{n \to \infty} \frac{\log_2 \log_2 a_n}{n} \geq 1$
-/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n, a n < a (n + 1)) ∧
  ∀ t : ℕ → ℕ, (∀ n, t n ≥ 1) →
    Irrational (∑' n : ℕ, 1 / ((t n : ℝ) * (a n : ℝ)))

/--
Hančl (1991): Irrationality sequences must satisfy
$\limsup_{n \to \infty} \frac{\log_2 \log_2 a_n}{n} \geq 1$.
-/
@[category research solved, AMS 11]
theorem erdos_262.hancl_lower_bound (a : ℕ → ℕ) (h : IsIrrationalitySequence a) :
    1 ≤ limsup (fun n : ℕ => (Real.log (Real.log (a n : ℝ)) / Real.log 2) / (n : ℝ)) atTop := by
  sorry

/--
More generally, if $a_n \ll 2^{2^{n-F(n)}}$ where $F(n) < n$ and $\sum 2^{-F(n)} < \infty$,
then $a_n$ cannot be an irrationality sequence.
-/
@[category research solved, AMS 11]
theorem erdos_262.general_obstruction (a : ℕ → ℕ) (F : ℕ → ℕ)
    (h_F : ∀ n, F n < n)
    (h_sum : Summable (fun n : ℕ => (2 : ℝ)^(-(F n : ℤ))))
    (h_bound : ∃ C > 0, ∀ n : ℕ, (a n : ℝ) ≤ C * (2 : ℝ)^((2 : ℝ)^((n : ℝ) - (F n : ℝ)))) :
    ¬ IsIrrationalitySequence a := by
  sorry

/--
Erdős proved that $a_n = 2^{2^n}$ is an irrationality sequence.
-/
@[category research solved, AMS 11]
theorem erdos_262.double_exponential :
    IsIrrationalitySequence (fun n : ℕ => 2^(2^n)) := by
  sorry

end Erdos262
