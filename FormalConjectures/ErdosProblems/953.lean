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
# Erdős Problem 953

Measurable sets with no integer distances.

OPEN

*Reference:* [erdosproblems.com/953](https://www.erdosproblems.com/953)
-/

open Finset MeasureTheory

open scoped Topology Real

namespace Erdos953

/-- Maximum measure of set with no integer distances -/
@[category research open, AMS 52]
theorem no_integer_distance_measure (r : ℝ) (answer : ℝ → ℝ) :
    ∃ (M : ℝ → ℝ),
      ∀ r > 0, M r = sSup {m : ℝ | ∃ (A : Set (ℝ × ℝ)),
        MeasurableSet A ∧
        A ⊆ {x | ‖x‖ < r} ∧
        volume A = ENNReal.ofReal m ∧
        ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∀ k : ℤ, ‖x - y‖ ≠ |k|} := by
  sorry

end Erdos953
