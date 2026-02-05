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
# Erdős Problem 459

Let f(u) be the largest v such that no m ∈ (u,v) is composed entirely of primes
dividing uv. Equivalently, v is the smallest number greater than u such that all
prime factors of v divide u.

Bounds: u + 2 ≤ f(u) ≤ u².
Special cases: f(p) = p² for prime p.
Cambie: SOLVED - For almost all n, f(n) = (1 + o(1))n.

*Reference:* [erdosproblems.com/459](https://www.erdosproblems.com/459)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos459

/-- f(u) is the largest v with required property -/
noncomputable def f (u : ℕ) : ℕ :=
  sSup {v : ℕ | v > u ∧ ∀ m : ℕ, u < m → m < v →
    ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ¬(p ∣ u * v)}

/-- Cambie: f(u) = (1+o(1))u for almost all u -/
@[category research solved, AMS 11]
theorem erdos_459_cambie :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      (Nat.card {u ≤ N | (f u : ℝ) < (1 + ε) * u} : ℝ) > (1 - ε) * N := by
  sorry

/-- f(p) = p² for primes -/
@[category research solved, AMS 11]
theorem erdos_459_prime :
    ∀ p : ℕ, p.Prime → f p = p^2 := by
  sorry

end Erdos459
