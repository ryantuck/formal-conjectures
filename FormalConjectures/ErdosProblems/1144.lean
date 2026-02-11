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

This problem concerns the behavior of partial sums of random completely multiplicative
functions where the function values at primes are uniformly chosen from {-1, 1}.
The question asks whether, for almost every such random function, the partial sums
exhibit unbounded growth when normalized by √N, specifically whether they can exceed
any given bound infinitely often (a form of the law of the iterated logarithm).

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

/-- For random completely multiplicative functions with values ±1 at primes,
    the partial sums (normalized by √N) grow unboundedly for almost every realization.
    More precisely, for almost every such function f, and for any bound M, there are
    infinitely many N where the normalized partial sum exceeds M. -/
@[category research open, AMS 11]
theorem random_multiplicative_function_sums :
    answer(sorry) ↔ ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
      (f : Ω → ℕ → ℤ),
      (∀ ω, IsCompletelyMultiplicative (f ω)) →
      (∀ p : ℕ, Nat.Prime p → ∀ ω, f ω p ∈ ({-1, 1} : Set ℤ)) →
      ∀ᵐ ω, ∀ M : ℝ, ∃ᶠ N in Filter.atTop, (partialSum (f ω) N : ℝ) / Real.sqrt N > M := by
  sorry

end Erdos1144
