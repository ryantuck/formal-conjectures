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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 27

*Reference:* [erdosproblems.com/27](https://www.erdosproblems.com/27)
-/

namespace Erdos27

open scoped BigOperators

/--
An $\epsilon$-almost covering system is a set of congruences $a_i \pmod{n_i}$ for distinct moduli
$n_1 < \dots < n_k$ such that the density of those integers which satisfy none of them is $\leq \epsilon$.

Is there a constant $C > 1$ such that for every $\epsilon > 0$ and $N \ge 1$ there is an
$\epsilon$-almost covering system with $N \le n_1 < \dots < n_k \le CN$?

The answer is no, as proved by Filaseta, Ford, Konyagin, Pomerance, and Yu [FFKPY07].

[FFKPY07] M. Filaseta, K. Ford, S. Konyagin, C. Pomerance, and G. Yu,
_Sieving by large integers and covering systems of congruences_, J. Amer. Math. Soc. 20 (2007), 495–517.
-/
@[category research solved, AMS 11]
theorem erdos_27 : answer(False) ↔ ∃ C > 1, ∀ ε > 0, ∀ N ≥ 1,
    ∃ (k : ℕ) (n a : Fin k → ℕ),
      Function.Injective n ∧
      (∀ i, n i ∈ Set.Icc N (Nat.floor (C * (N : ℝ)))) ∧
      ∃ (U : Set ℕ),
        U = {x | ∀ i, x % n i ≠ a i % n i} ∧
        ∃ d, U.HasDensity d ∧ d ≤ ε := by
  sorry

end Erdos27
