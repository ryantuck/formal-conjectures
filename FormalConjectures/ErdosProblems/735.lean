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
# Erdős Problem 735

Weighted points on lines - Murty's conjecture.

SOLVED

*Reference:* [erdosproblems.com/735](https://www.erdosproblems.com/735)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos735

/-- Only four configurations allow equal weight sums on all lines -/
@[category research solved, AMS 52]
theorem weighted_points_equal_lines :
    ∀ (n : ℕ) (pts : Finset (Fin 2 → ℝ)) (w : (Fin 2 → ℝ) → ℝ),
      pts.card = n →
      (∀ p ∈ pts, w p > 0) →
      (∀ L : Finset (Fin 2 → ℝ), L ⊆ pts → L.card ≥ 2 →
        sorry) →
      sorry := by
  sorry

end Erdos735
