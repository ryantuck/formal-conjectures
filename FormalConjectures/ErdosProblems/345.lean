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
# Erdős Problem 345

Let A ⊆ ℕ be a complete sequence, with the threshold of completeness T(A) defined as the
least integer m such that all n ≥ m belong to P(A) = {Σ_{n∈B} n : B ⊆ A finite}.

Question: Are there infinitely many k such that T(nᵏ) > T(nᵏ⁺¹)?

Known values:
- T(n) = 1
- T(n²) = 128
- T(n³) = 12758
- T(n⁴) = 5134240
- T(n⁵) = 67898771

OPEN: Examining k = 2^t for large t is suggested as promising.

*Reference:* [erdosproblems.com/345](https://www.erdosproblems.com/345)
-/

open Filter Topology BigOperators Real

namespace Erdos345

/-- The set of subset sums -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.sum id = n}

/-- A set is complete if all sufficiently large integers are subset sums -/
def IsComplete (A : Set ℕ) : Prop :=
  ∃ m : ℕ, ∀ n ≥ m, n ∈ subsetSums A

/-- The threshold of completeness -/
def HasThreshold (A : Set ℕ) (T : ℕ) : Prop :=
  (∀ n ≥ T, n ∈ subsetSums A) ∧ (∀ T' < T, ∃ n ≥ T', n ∉ subsetSums A)

/-- Set of k-th powers -/
def powers (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ m : ℕ, n = m ^ k}

/-- Main question: Infinitely many k with T(nᵏ) > T(nᵏ⁺¹)? -/
@[category research open, AMS 11]
theorem erdos_345_main :
    ∃ᶠ k in atTop, ∃ T_k T_k1 : ℕ,
      HasThreshold (powers k) T_k ∧ HasThreshold (powers (k + 1)) T_k1 ∧ T_k > T_k1 := by
  sorry

/-- Known values -/
@[category research open, AMS 11]
theorem erdos_345_known_values :
    HasThreshold (powers 1) 1 ∧
    HasThreshold (powers 2) 128 ∧
    HasThreshold (powers 3) 12758 ∧
    HasThreshold (powers 4) 5134240 ∧
    HasThreshold (powers 5) 67898771 := by
  sorry

end Erdos345
