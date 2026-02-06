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

/-- The Duffin-Schaeffer conjecture -/
@[category research solved, AMS 11]
theorem duffin_schaeffer (f : ℕ → ℕ) :
    (∀ᵐ α, ∃ᶠ (p, q) : ℕ × ℕ in atTop,
      Nat.Coprime p q ∧ |α - p / q| < (f q : ℝ) / q) ↔
    (∑' q : ℕ, (Nat.totient q * f q : ℝ) / q) = ∞ := by
  sorry

end Erdos999
