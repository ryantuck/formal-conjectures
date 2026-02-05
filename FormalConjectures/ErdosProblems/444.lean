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
# Erdős Problem 444

Let A ⊆ ℕ be an infinite set, and let dₐ(n) denote the count of elements in A that
divide n. For every positive integer k, is

  limsup_{x → ∞} (max_{n<x} dₐ(n)) / (∑_{n ∈ A ∩ [1,x)} 1/n)^k = ∞ ?

Erdős-Sárkőzy: PROVED - The answer is affirmative.

*Reference:* [erdosproblems.com/444](https://www.erdosproblems.com/444)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos444

/-- dₐ(n) counts divisors from set A -/
noncomputable def d_A (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.card {a ∈ A | a ∣ n}

/-- Erdős-Sárkőzy: Divisor count grows faster than harmonic sum power -/
@[category research solved, AMS 11]
theorem erdos_444_erdos_sarkozy :
    ∀ A : Set ℕ, A.Infinite → ∀ k : ℕ, k > 0 →
      ∀ M : ℝ, ∃ᶠ x : ℕ in atTop, ∃ n < x,
        M * (((Finset.range x).filter (· ∈ A)).sum (fun m => (1 : ℝ) / (m + 1))) ^ k ≤ d_A A n := by
  sorry

end Erdos444
