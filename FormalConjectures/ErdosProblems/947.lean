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
# Erdős Problem 947

No exact covering system exists.

PROVED

*Reference:* [erdosproblems.com/947](https://www.erdosproblems.com/947)
-/

open Finset

open scoped Topology Real

namespace Erdos947

/-- Covering system with distinct odd moduli -/
def CoveringSystem (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ (m r) ∈ S, Odd m ∧ r < m) ∧
  (∀ (m₁ r₁) ∈ S, ∀ (m₂ r₂) ∈ S, (m₁, r₁) ≠ (m₂, r₂) → m₁ ≠ m₂) ∧
  (∀ n : ℕ, ∃ (m r) ∈ S, n ≡ r [MOD m])

/-- No covering system with distinct odd moduli exists -/
@[category research solved, AMS 11]
theorem no_odd_covering :
    ¬ ∃ (S : Finset (ℕ × ℕ)), CoveringSystem S := by
  sorry

end Erdos947
