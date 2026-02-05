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
# Erdős Problem 433

For a finite set A ⊂ ℕ, let G(A) denote the greatest integer not expressible as a finite
sum of elements from A (with repetitions allowed). Define:

  g(k,n) = max G(A)

where the maximum is taken over all A ⊆ {1,...,n} with |A| = k and no common divisor.

Is it true that g(k,n) ~ n²/(k-1)?

Dixmier (1990): PROVED - Determined exact bounds:
  ⌊(n-2)/(k-1)⌋(n-k+1)-1 ≤ g(k,n) ≤ (⌊(n-1)/(k-1)⌋-1)n-1

*Reference:* [erdosproblems.com/433](https://www.erdosproblems.com/433)
-/

open Filter Topology BigOperators Real

namespace Erdos433

/-- G(A) is the greatest integer not expressible as sum from A -/
noncomputable def G (A : Finset ℕ) : ℕ :=
  sSup {m : ℕ | ∀ S : Multiset ℕ, (∀ a ∈ S, a ∈ A) → S.sum ≠ m}

/-- g(k,n) is the maximum G(A) over sets of size k -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {G A | (A : Finset ℕ) (_h : A.card = k ∧ (∀ a ∈ A, 0 < a ∧ a ≤ n) ∧
    (A : Set ℕ).ncard.gcd (A : Set ℕ).ncard = 1)}

/-- Dixmier: Exact bounds for g(k,n) -/
@[category research solved, AMS 11]
theorem erdos_433_dixmier :
    ∀ k n : ℕ, 2 ≤ k → k < n →
      (n - 2) / (k - 1) * (n - k + 1) - 1 ≤ g k n ∧
      g k n ≤ ((n - 1) / (k - 1) - 1) * n - 1 := by
  sorry

/-- Erdős-Graham: g(k,n) is asymptotic to n²/(k-1) -/
@[category research solved, AMS 11]
theorem erdos_433_asymptotic :
    ∀ k : ℕ, k ≥ 2 →
      Tendsto (fun n => (g k n : ℝ) / ((n : ℝ)^2 / (k - 1 : ℝ))) atTop (𝓝 1) := by
  sorry

end Erdos433
