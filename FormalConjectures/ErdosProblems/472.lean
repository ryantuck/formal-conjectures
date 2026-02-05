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
# Erdős Problem 472

Given an initial finite sequence of primes q₁ < ... < qₘ, extend it so that qₙ₊₁ is
the smallest prime of the form qₙ + qᵢ - 1 for n ≥ m. Does there exist an initial
starting sequence such that the resulting sequence is infinite?

Ulam's problem. Example: Starting with 3, 5 yields 3, 5, 7, 11, 13, 17, ...

*Reference:* [erdosproblems.com/472](https://www.erdosproblems.com/472)
-/

open Filter Topology BigOperators Real Classical

namespace Erdos472

/-- Ulam's conjecture -/
@[category research open, AMS 11]
theorem erdos_472 :
    ∃ init : List ℕ, init ≠ [] ∧ (∀ p ∈ init, p.Prime) ∧ init.Sorted (· < ·) ∧
      ∃ seq : ℕ → ℕ, (∀ i : ℕ, ∀ h : i < init.length, seq i = init.get ⟨i, h⟩) ∧
        (∀ n : ℕ, n ≥ init.length → seq n = sInf {p : ℕ | p.Prime ∧
          ∃ i < n, seq n = seq (n - 1) + seq i - 1}) ∧
        ∀ M : ℕ, ∃ n : ℕ, seq n > M := by
  sorry

end Erdos472
