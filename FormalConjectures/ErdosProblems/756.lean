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
# Erdős Problem 756

Distinct distances with high multiplicity.

PROVED

*Reference:* [erdosproblems.com/756](https://www.erdosproblems.com/756)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos756

/-- Set has many distances each occurring >n times -/
@[category research solved, AMS 52]
theorem many_distances_high_multiplicity (answer : Prop) :
    answer ↔ ∀ (n : ℕ),
      ∃ (A : Finset (Fin 2 → ℝ)),
        A.card = n ∧
        ∃ (D : Finset ℝ), D.card ≥ sorry ∧
          ∀ d ∈ D, sorry := by
  sorry

end Erdos756
