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
# Erdős Problem 532: Hindman's Theorem

If the natural numbers are 2-colored, does there exist an infinite set A ⊆ ℕ
such that all finite subset sums are monochromatic?

SOLVED: Proved by Hindman (1974) for any finite number of colors.

*Reference:* [erdosproblems.com/532](https://www.erdosproblems.com/532)
-/

open Set Finset

namespace Erdos532

/-- Hindman's theorem: any finite coloring has an infinite monochromatic IP set -/
@[category research solved, AMS 05 11]
theorem hindman_theorem (r : ℕ) (hr : r > 0) :
    ∀ (c : ℕ → Fin r), ∃ (A : Set ℕ) (col : Fin r),
      A.Infinite ∧
      ∀ (S : Finset ℕ), (S : Set ℕ) ⊆ A → S.Nonempty →
        c (∑ n ∈ S, n) = col := by
  sorry

/-- Two-color case of Hindman's theorem -/
@[category research solved, AMS 05 11]
theorem hindman_two_colors :
    ∀ (c : ℕ → Fin 2), ∃ (A : Set ℕ) (col : Fin 2),
      A.Infinite ∧
      ∀ (S : Finset ℕ), (S : Set ℕ) ⊆ A → S.Nonempty →
        c (∑ n ∈ S, n) = col := by
  sorry

end Erdos532
