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
# Erdős Problem 449

Let r(n) count pairs of divisors (d₁, d₂) where d₁ | n, d₂ | n, and d₁ < d₂ < 2d₁.
Is r(n) < ε·τ(n) for almost all n, for every ε > 0?

DISPROVED - For any K > 0, there exists a positive density set of integers n
with r(n) > K·τ(n). Follows from Problem 448 using Cauchy-Schwarz.

*Reference:* [erdosproblems.com/449](https://www.erdosproblems.com/449)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos449

/-- r(n) counts close divisor pairs -/
noncomputable def r (n : ℕ) : ℕ :=
  Nat.card {p : ℕ × ℕ | p.1 ∣ n ∧ p.2 ∣ n ∧ p.1 < p.2 ∧ p.2 < 2 * p.1}

/-- Disproof: positive density with large r(n) -/
@[category research solved, AMS 11]
theorem erdos_449_disproved :
    ∀ K : ℝ, K > 0 → ∃ c : ℝ, c > 0 ∧
      limsup (fun N : ℕ => (Nat.card {n ≤ N | K * (n.divisors.card : ℝ) < r n} : ℝ) / N) atTop ≥ c := by
  sorry

end Erdos449
