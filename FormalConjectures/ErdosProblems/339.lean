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
# Erdős Problem 339

Let A ⊆ ℕ be a basis of order r. Must the set of integers representable as the sum of
exactly r distinct elements from A have positive lower density?

Also: If the set of integers which are the sum of r elements from A has positive upper
density, must the set of integers representable as the sum of exactly r distinct elements
have positive upper density?

PROVED: Both questions answered affirmatively by Hegyvári, Hennecart, and Plagne (2003).

*Reference:* [erdosproblems.com/339](https://www.erdosproblems.com/339)
-/

open Filter Topology BigOperators MeasureTheory Real

namespace Erdos339

/-- A is a basis of order r -/
def IsBasisOfOrder (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card ≤ r ∧ S.sum id = n

/-- Set of integers representable as sum of exactly r distinct elements from A -/
def RDistinctSums (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card = r ∧ S.sum id = n}

/-- Set of integers representable as sum of exactly r elements from A (with repetition) -/
def RSums (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.card = r ∧ S.sum id = n}

/-- Lower density -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (fun N => (Nat.card {n ∈ S | n ≤ N} : ℝ) / N) atTop

/-- Upper density -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (Nat.card {n ∈ S | n ≤ N} : ℝ) / N) atTop

/-- Hegyvári-Hennecart-Plagne: Distinct sums have positive lower density -/
@[category research solved, AMS 11]
theorem erdos_339_main (A : Set ℕ) (r : ℕ) :
    IsBasisOfOrder A r → lowerDensity (RDistinctSums A r) > 0 := by
  sorry

/-- Hegyvári-Hennecart-Plagne: Upper density version -/
@[category research solved, AMS 11]
theorem erdos_339_upper (A : Set ℕ) (r : ℕ) :
    IsBasisOfOrder A r → upperDensity (RSums A r) > 0 →
      upperDensity (RDistinctSums A r) > 0 := by
  sorry

end Erdos339
