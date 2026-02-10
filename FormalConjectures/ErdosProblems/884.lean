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
# Erdős Problem 884

Divisor reciprocal difference sum bound.

OPEN

*Reference:* [erdosproblems.com/884](https://www.erdosproblems.com/884)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos884

/-- The divisors of n as a finset -/
def divisors (n : ℕ) : Finset ℕ := n.divisors

/-- Sum of reciprocals of all pairwise divisor differences -/
noncomputable def allPairwiseDiffSum (n : ℕ) : ℝ :=
  ∑ d₁ ∈ divisors n, ∑ d₂ ∈ divisors n,
    if d₁ < d₂ then (1 : ℝ) / (d₂ - d₁) else 0

/-- Sum of reciprocals of consecutive divisor differences -/
noncomputable def consecutiveDiffSum (n : ℕ) : ℝ :=
  let divList := (divisors n).sort (·  ≤ ·)
  ∑ i ∈ Finset.range (divList.length - 1),
    if h : i + 1 < divList.length then
      (1 : ℝ) / (divList.get ⟨i + 1, h⟩ - divList.get ⟨i, Nat.lt_of_succ_lt h⟩)
    else 0

/-- Main question: Is ∑_{i<j} 1/(dⱼ-dᵢ) ≪ 1 + ∑ᵢ 1/(dᵢ₊₁-dᵢ) with absolute constant? -/
@[category research open, AMS 11]
theorem divisor_reciprocal_inequality :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      allPairwiseDiffSum n ≤ C * (1 + consecutiveDiffSum n) := by
  sorry

end Erdos884
