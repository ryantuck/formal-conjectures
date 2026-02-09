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
# Erdős Problem 670

Let A ⊆ ℝ^d be n points with all pairwise distances differing by at least 1.
Is the diameter at least (1+o(1))n²?

OPEN (Erdős proved it for d=1)

*Reference:* [erdosproblems.com/670](https://www.erdosproblems.com/670)
-/

open EuclideanSpace Metric Finset Filter

open scoped Topology Real

namespace Erdos670

variable {d : ℕ}

/-- Diameter of set -/
noncomputable def diameter (A : Finset (Fin d → ℝ)) : ℝ := sorry

/-- Pairwise distances differ by ≥ 1 implies diameter ≥ (1+o(1))n² -/
@[category research open, AMS 52]
theorem distance_separation_implies_large_diameter (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (A : Finset (Fin d → ℝ)), A.card = n →
        (∀ x y z w, x ∈ A → y ∈ A → z ∈ A → w ∈ A →
          (x, y) ≠ (z, w) → |dist x y - dist z w| ≥ 1) →
        diameter A ≥ (1 - ε) * n^2 := by
  sorry

end Erdos670
