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
# Erdős Problem 443

For integers m, n ≥ 1, determine the cardinality of the intersection:
  #{k(m-k) : 1 ≤ k ≤ m/2} ∩ {l(n-l) : 1 ≤ l ≤ n/2}

Can this be arbitrarily large? Does it satisfy ≤ (mn)^(o(1))?

Hegyvári-Cambie: PROVED (Lean verified) - When m > n, the intersection has size
bounded by m^(O(1/log log m)). For any integer s, there exist infinitely many pairs
(m,n) such that the intersection contains exactly s elements.

*Reference:* [erdosproblems.com/443](https://www.erdosproblems.com/443)
-/

open Filter Topology BigOperators Real

namespace Erdos443

/-- The set of products k(m-k) for k in range -/
def productSet (m : ℕ) : Set ℕ :=
  {p : ℕ | ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ m ∧ p = k * (m - k)}

/-- Hegyvári-Cambie: Upper bound on intersection -/
@[category research solved, AMS 11]
theorem erdos_443_hegyvar_cambie_bound :
    ∀ m n : ℕ, m > n → n ≥ 1 →
      ∃ C : ℝ, C > 0 ∧
        (Nat.card (Set.inter (productSet m) (productSet n)) : ℝ) ≤
          m ^ (C / log (log m)) := by
  sorry

/-- Hegyvári-Cambie: Density result -/
@[category research solved, AMS 11]
theorem erdos_443_hegyvar_cambie_density :
    ∀ s : ℕ, ∀ M : ℕ, ∃ m n : ℕ, m > M ∧
      Nat.card (Set.inter (productSet m) (productSet n)) = s := by
  sorry

end Erdos443
