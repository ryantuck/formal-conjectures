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
# Erdős Problem 468

For integer n, define Dₙ as the set of partial sums of divisors:
d₁, d₁+d₂, d₁+d₂+d₃, ... where 1 < d₁ < d₂ < ... are the divisors of n.

Questions:
1. What is the size of Dₙ \ ∪_{m<n} Dₘ?
2. If f(N) is the minimal n with N ∈ Dₙ, is f(N) = o(N)? Perhaps for almost all N?

*Reference:* [erdosproblems.com/468](https://www.erdosproblems.com/468)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos468

/-- Dₙ is the set of partial divisor sums -/
noncomputable def D (n : ℕ) : Set ℕ :=
  {s : ℕ | ∃ k : ℕ, ∃ divs : Fin k → ℕ,
    StrictMono divs ∧ (∀ i, divs i ∣ n ∧ divs i > 1) ∧
    s = (Finset.univ.image divs).sum id}

/-- f(N) is the minimal n with N ∈ Dₙ -/
noncomputable def f (N : ℕ) : ℕ :=
  sInf {n : ℕ | N ∈ D n}

/-- Question 2: f(N) = o(N) for almost all N -/
@[category research open, AMS 11]
theorem erdos_468_q2 :
    ∀ ε > 0, ∀ᶠ M : ℕ in atTop,
      (Nat.card {N ≤ M | (f N : ℝ) < ε * N} : ℝ) > (1 - ε) * M := by
  sorry

end Erdos468
