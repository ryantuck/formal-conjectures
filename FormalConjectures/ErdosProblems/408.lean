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
# Erdős Problem 408

Let φ_k(n) be the k-fold iteration of Euler's totient function.
Define f(n) = min{k : φ_k(n) = 1}.

Question 1: Does f(n)/log n have a distribution function?
Question 2: Is f(n)/log n almost always constant?
Question 3: What about the largest prime factor of φ_k(n) when k = log log n?

Pillai: log₃ n < f(n) < log₂ n for large n.
Erdős-Granville-Pomerance-Spiro: Conditionally YES to questions 1-2 (assuming Elliott-Halberstam).

*Reference:* [erdosproblems.com/408](https://www.erdosproblems.com/408)
-/

open Filter Topology BigOperators Real

namespace Erdos408

/-- k-fold iteration of Euler's totient function -/
def φ_iter : ℕ → ℕ → ℕ
  | 0, n => n
  | k+1, n => Nat.totient (φ_iter k n)

/-- f(n) is the minimal iterations to reach 1 -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | φ_iter k n = 1}

/-- Pillai: Bounds on f(n) -/
@[category research open, AMS 11]
theorem erdos_408_pillai :
    ∀ᶠ n : ℕ in atTop,
      log n / log 3 < (f n : ℝ) ∧ (f n : ℝ) < log n / log 2 := by
  sorry

end Erdos408
