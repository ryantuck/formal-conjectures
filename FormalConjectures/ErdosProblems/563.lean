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

/-!
# Erdős Problem 563

*Reference:* [erdosproblems.com/563](https://www.erdosproblems.com/563)

## Statement (OPEN)
Let F(n,α) denote the smallest m such that there exists a 2-colouring of the edges of K_n
so that every X ⊆ [n] with |X| ≥ m contains more than α(|X| choose 2) many edges of each colour.

Conjecture: For every 0 ≤ α < 1/2, F(n,α) ~ c_α log n for some constant c_α depending only on α.

## Source
[Er90b, p.21]
-/

open SimpleGraph Filter Asymptotics

open scoped Topology Real

namespace Erdos563

/-- F(n,α) is the smallest m such that there exists a 2-colouring of the edges of K_n
    where every subset X of size ≥ m has more than α|X|(|X|-1)/2 edges of each colour -/
def F (n : ℕ) (α : ℝ) : ℕ := sorry

/-- Main conjecture: For 0 ≤ α < 1/2, F(n,α) ~ c_α log n -/
@[category research open, AMS 05]
theorem f_asymptotic_log (α : ℝ) (hα : 0 ≤ α ∧ α < 1/2) :
    ∃ c : ℝ, c > 0 ∧ (fun n => (F n α : ℝ)) ~[atTop] fun n => c * Real.log n :=
  sorry

end Erdos563
