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
import Mathlib.Data.Nat.Factors

/-!
# Erdős Problem 205

*Reference:* [erdosproblems.com/205](https://www.erdosproblems.com/205)
-/

open Filter
open scoped Topology Real

namespace Erdos205

/--
$\Omega(m)$ is the number of prime divisors of $m$ counted with multiplicity.
-/
def Omega (m : ℕ) : ℕ := m.primeFactorsList.length

/--
Is it true that all sufficiently large $n$ can be written as $2^k+m$ for some $k \geq 0$,
where $\Omega(m) < \log \log m$?
-/
@[category research solved, AMS 11]
theorem erdos_205 : answer(False) ↔ ∀ᶠ (n : ℕ) in atTop, ∃ (k : ℕ) (m : ℕ),
    n = 2^k + m ∧ (Omega m : ℝ) < Real.log (Real.log m) := by
  sorry

/--
Quantified negative answer by Tao and Alexeev:
There are infinitely many $n$ such that for all $k$ with $2^k < n$, $n - 2^k$ has at least
$\gg (\frac{\log n}{\log \log n})^{1/2}$ many prime factors.
-/
@[category research solved, AMS 11]
theorem erdos_205.variants.tao_alexeev : ∃ C > 0, ∀ (N : ℕ), ∃ n ≥ N,
    ∀ (k : ℕ), 2^k < n → (Omega (n - 2^k) : ℝ) ≥ C * Real.sqrt (Real.log n / Real.log (Real.log n)) := by
  sorry

end Erdos205