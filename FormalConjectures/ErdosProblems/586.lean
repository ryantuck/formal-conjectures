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
# Erdős Problem 586

Is there a covering system such that no two of the moduli divide each other?

DISPROVED by Balister, Bollobas, Morris, Sahasrabudhe, and Tiba

*Reference:* [erdosproblems.com/586](https://www.erdosproblems.com/586)
-/

open Nat

open scoped Topology Real

namespace Erdos586

/-- A covering system is a collection of congruences covering all integers -/
def IsCoveringSystem (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ am ∈ S, am.2 > 0) ∧
  (∀ n : ℤ, ∃ am ∈ S, n ≡ am.1 [ZMOD am.2])

/-- No covering system has pairwise non-divisible moduli -/
@[category research solved, AMS 11]
theorem no_covering_system_nondivisible_moduli :
    ¬ ∃ (S : Finset (ℕ × ℕ)), IsCoveringSystem S ∧
      (∀ (a₁ m₁) (a₂ m₂), (a₁, m₁) ∈ S → (a₂, m₂) ∈ S → (a₁, m₁) ≠ (a₂, m₂) →
        ¬ (m₁ ∣ m₂) ∧ ¬ (m₂ ∣ m₁)) := by
  sorry

end Erdos586
