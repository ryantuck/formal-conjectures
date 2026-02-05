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
# Erdős Problem 338

The restricted order of a basis A is the smallest integer t such that every sufficiently
large integer can be expressed as a sum of at most t distinct elements from A.

Questions:
- What conditions ensure a restricted order exists?
- Can it be bounded in terms of the ordinary order?
- When does restricted order equal ordinary order?

Known results:
- Bateman: Bases of order h ≥ 3 may lack restricted order.
- Kelly: Any order-2 basis has restricted order ≤ 4 (conjectured ≤ 3).
- Hennecart: Disproved Kelly's conjecture with construction achieving restricted order 4.
- Perfect squares: order 4, restricted order 5.
- Triangular numbers: order 3, restricted order 3.
- Hegyvári-Hennecart-Plagne: For all k ≥ 2, there exist bases of order k with
  restricted order ≥ 2^(k-2) + k - 1.

Open: Does A \ F remains a basis for all finite F imply A has a restricted order?

*Reference:* [erdosproblems.com/338](https://www.erdosproblems.com/338)
-/

open Filter Topology BigOperators Real

namespace Erdos338

/-- A is a basis of order h if every large n is a sum of at most h elements from A -/
def IsBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card ≤ h ∧ S.sum id = n

/-- A has restricted order t if every large n is a sum of at most t distinct elements from A -/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card ≤ t ∧ S.sum id = n

/-- Kelly: Any order-2 basis has restricted order at most 4 -/
@[category research solved, AMS 11]
theorem erdos_338_kelly :
    ∀ A : Set ℕ, IsBasisOfOrder A 2 →
      ∃ t ≤ 4, HasRestrictedOrder A t := by
  sorry

/-- Hennecart: There exists an order-2 basis with restricted order 4 -/
@[category research solved, AMS 11]
theorem erdos_338_hennecart :
    ∃ A : Set ℕ, IsBasisOfOrder A 2 ∧
      HasRestrictedOrder A 4 ∧ ¬HasRestrictedOrder A 3 := by
  sorry

/-- Hegyvári-Hennecart-Plagne: Lower bounds on restricted order -/
@[category research solved, AMS 11]
theorem erdos_338_hhp (k : ℕ) (hk : k ≥ 2) :
    ∃ A : Set ℕ, IsBasisOfOrder A k ∧
      ∀ t < 2^(k-2) + k - 1, ¬HasRestrictedOrder A t := by
  sorry

end Erdos338
