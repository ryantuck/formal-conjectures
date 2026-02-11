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
# Erdős Problem 1144

Random completely multiplicative functions and partial sums.

OPEN

*Reference:* [erdosproblems.com/1144](https://www.erdosproblems.com/1144)
-/

open Finset Filter MeasureTheory

open scoped Topology Real

namespace Erdos1144

/-- A completely multiplicative function -/
def IsCompletelyMultiplicative (f : ℕ → ℤ) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, f (m * n) = f m * f n

/-- Partial sum of a multiplicative function -/
def partialSum (f : ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ m ∈ Finset.range N, f (m + 1)

/-- Random completely multiplicative functions and partial sums -/
@[category research open, AMS 11]
theorem random_multiplicative_function_sums (answer : Prop) :
    answer ↔ ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
      (f : Ω → ℕ → ℤ),
      (∀ ω, IsCompletelyMultiplicative (f ω)) →
      (∀ p : ℕ, Nat.Prime p → ∀ ω, f ω p ∈ ({-1, 1} : Set ℤ)) →
      ∀ᵐ ω, ∀ M : ℝ, ∃ᶠ N in Filter.atTop, (partialSum (f ω) N : ℝ) / Real.sqrt N > M := by
  sorry

end Erdos1144
