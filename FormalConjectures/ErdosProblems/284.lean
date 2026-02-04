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
# Erdős Problem 284

*Reference:* [erdosproblems.com/284](https://www.erdosproblems.com/284)
-/

open Filter Topology

namespace Erdos284

/--
Let $f(k)$ denote the maximum value of $n_1$ such that there exist $n_1 < n_2 < \cdots < n_k$
satisfying: $1 = \frac{1}{n_1} + \cdots + \frac{1}{n_k}$.

Conjecture: $f(k) = (1+o(1))\frac{k}{e-1}$.

This was essentially solved by Croot (2001).
-/
noncomputable def f (k : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ (a : Fin k → ℕ), (∀ i, a i ≥ n) ∧
    (∀ i j, i < j → a i < a j) ∧ (1 : ℝ) = ∑ i : Fin k, (1 : ℝ) / (a i : ℝ)}

/--
Trivial upper bound: $f(k) \leq (1+o(1))\frac{k}{e-1}$.
-/
@[category research solved, AMS 11]
theorem erdos_284_upper_bound :
    ∃ C > 0, ∀ k : ℕ, k ≥ 1 → (f k : ℝ) ≤ (1 + C / k) * (k : ℝ) / (Real.exp 1 - 1) := by
  sorry

/--
Croot (2001): For any $N > 1$, there exists $k \geq 1$ with
$N < n_1 < \cdots < n_k \leq (e+o(1))N$ where $1 = \sum \frac{1}{n_i}$.

This essentially solves the conjecture.
-/
@[category research solved, AMS 11]
theorem erdos_284_croot (N : ℕ) (hN : N > 1) :
    ∃ k : ℕ, ∃ (a : Fin k → ℕ),
      (∀ i, N < a i ∧ (a i : ℝ) ≤ (Real.exp 1 + 1) * (N : ℝ)) ∧
      (∀ i j, i < j → a i < a j) ∧
      (1 : ℝ) = ∑ i : Fin k, (1 : ℝ) / (a i : ℝ) := by
  sorry

/--
The conjecture: $f(k) = (1+o(1))\frac{k}{e-1}$.
-/
@[category research solved, AMS 11]
theorem erdos_284 :
    Tendsto (fun k : ℕ => ((f k : ℝ) * (Real.exp 1 - 1)) / (k : ℝ)) atTop (𝓝 1) := by
  sorry

end Erdos284
