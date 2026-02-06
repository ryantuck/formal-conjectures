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
# Erdős Problem 661

Are there, for all large n, points x₁,...,xₙ,y₁,...,yₙ ∈ ℝ² such that the number
of distinct distances d(xᵢ,yⱼ) is o(n/√(log n))?

OPEN ($50 reward)

*Reference:* [erdosproblems.com/661](https://www.erdosproblems.com/661)
-/

open EuclideanSpace Metric Finset

open scoped Topology Real

namespace Erdos661

/-- Bipartite distance problem: o(n/√(log n)) distinct distances -/
@[category research open, AMS 52]
theorem bipartite_few_distances (answer : Prop) :
    answer ↔ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ (X Y : Finset (Fin 2 → ℝ)), X.card = n ∧ Y.card = n ∧
        ∀ ε > 0, (X ×ˢ Y).image (fun (x, y) => dist x y) |>.card
          < Nat.floor (ε * n / Real.sqrt (Real.log n)) := by
  sorry

end Erdos661
