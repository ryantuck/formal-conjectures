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

/-- A line in ℝ² -/
def IsLine (L : Set (ℝ × ℝ)) : Prop :=
  ∃ (a b c : ℝ), (a ≠ 0 ∨ b ≠ 0) ∧ L = {p : ℝ × ℝ | a * p.1 + b * p.2 = c}

/-- Line determined by two distinct points is ordinary for a point set -/
def IsOrdinaryLine (A : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : Prop :=
  p ≠ q ∧ p ∈ A ∧ q ∈ A ∧
  ∀ r ∈ A, r ≠ p → r ≠ q →
    ¬∃ (L : Set (ℝ × ℝ)), IsLine L ∧ p ∈ L ∧ q ∈ L ∧ r ∈ L

/-- Threshold for existence of r points with all ordinary lines -/
@[category research open, AMS 52]
theorem ordinary_lines_threshold (r k : ℕ) :
    ∃ (f : ℕ → ℕ → ℕ),
      ∀ n : ℕ, ∀ (A : Finset (ℝ × ℝ)),
        A.card = n →
        (∀ L : Set (ℝ × ℝ), IsLine L → {p : ℝ × ℝ | p ∈ A ∧ p ∈ L}.ncard < k) →
        f r k ≤ {pq : (ℝ × ℝ) × (ℝ × ℝ) | IsOrdinaryLine A pq.1 pq.2}.ncard →
        ∃ (A' : Finset (ℝ × ℝ)),
          A' ⊆ A ∧ A'.card = r ∧
          ∀ p ∈ A', ∀ q ∈ A', p ≠ q → IsOrdinaryLine A p q := by
  sorry

end Erdos960
