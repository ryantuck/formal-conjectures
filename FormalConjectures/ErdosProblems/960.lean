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
# Erdős Problem 960

Ordinary lines in point sets.

OPEN

*Reference:* [erdosproblems.com/960](https://www.erdosproblems.com/960)
-/

open Finset

open scoped Topology Real

namespace Erdos960

/-- Threshold for existence of r points with all ordinary lines -/
@[category research open, AMS 52]
theorem ordinary_lines_threshold (r k : ℕ) (answer : ℕ → ℕ) :
    ∃ (f : ℕ → ℕ → ℕ),
      ∀ n : ℕ, ∀ (A : Finset (ℝ × ℝ)),
        A.card = n →
        (∀ L : Set (ℝ × ℝ), sorry → (A ∩ L).card < k) →
        f r k n ≤ {L : Set (ℝ × ℝ) | sorry ∧ (A ∩ L).card = 2}.ncard →
        ∃ (A' : Finset (ℝ × ℝ)),
          A' ⊆ A ∧ A'.card = r ∧
          ∀ p q : ℝ × ℝ, p ∈ A' → q ∈ A' → p ≠ q →
            sorry := by
  sorry

end Erdos960
