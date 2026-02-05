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
# Erdős Problem 308

For $N \geq 1$, determine the smallest integer not representable as a sum of distinct
unit fractions with denominators from $\{1, \ldots, N\}$. Additionally, investigate
whether the set of representable integers always has the form $\{1, \ldots, m\}$ for some $m$.

Croot proved bounds showing that for large $N$, the representable integers are either
$\{1, \ldots, m_N-1\}$ or $\{1, \ldots, m_N\}$ where $m_N = \lfloor \sum_{n \leq N} 1/n \rfloor$.

*Reference:* [erdosproblems.com/308](https://www.erdosproblems.com/308)
-/

open Filter Topology BigOperators

namespace Erdos308

/-- An integer k is representable using denominators up to N if it can be written
    as a sum of distinct unit fractions with denominators in {1,...,N} -/
def Representable (k N : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ n ≤ N) ∧ (k : ℚ) = S.sum (fun n => (1 : ℚ) / n)

/-- The smallest non-representable integer using denominators up to N -/
noncomputable def f (N : ℕ) : ℕ :=
  sInf {k : ℕ | k > 0 ∧ ¬Representable k N}

/-- The floor of the harmonic sum H_N = sum_{n=1}^N 1/n -/
noncomputable def m (N : ℕ) : ℕ :=
  ⌊(Finset.range N).sum (fun n => (1 : ℝ) / (n + 1))⌋₊

/-- Croot's lower bound for f(N) -/
@[category research solved, AMS 11]
theorem erdos_308_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
      (f N : ℝ) ≥ (Finset.range N).sum (fun n => (1 : ℝ) / (n + 1)) -
        (9/2) * c * (Real.log (Real.log N))^2 / Real.log N := by
  sorry

/-- Croot's upper bound for f(N) -/
@[category research solved, AMS 11]
theorem erdos_308_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (Finset.range N).sum (fun n => (1 : ℝ) / (n + 1)) -
        (1/2) * c * (Real.log (Real.log N))^2 / Real.log N := by
  sorry

/-- For large N, representable integers form {1,...,m_N-1} or {1,...,m_N} -/
@[category research solved, AMS 11]
theorem erdos_308_consecutive :
    ∀ᶠ N in atTop, f N = m N ∨ f N = m N + 1 := by
  sorry

end Erdos308
