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
# Erdős Problem 999

The Duffin-Schaeffer conjecture.

PROVED

*Reference:* [erdosproblems.com/999](https://www.erdosproblems.com/999)
-/

open Finset Filter MeasureTheory

open scoped Topology Real

namespace Erdos999

open scoped EReal in
/-- The Duffin-Schaeffer conjecture -/
@[category research solved, AMS 11]
theorem duffin_schaeffer (f : ℕ → ℕ) :
    (∀ᵐ α, ∃ᶠ pq : ℕ × ℕ in atTop,
      Nat.Coprime pq.1 pq.2 ∧ |α - (pq.1 : ℝ) / pq.2| < (f pq.2 : ℝ) / pq.2) ↔
    (∑' q : ℕ, ((Nat.totient q * f q : ℝ) / q : EReal)) = ⊤ := by
  sorry

end Erdos999
