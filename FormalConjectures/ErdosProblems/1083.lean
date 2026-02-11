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
# Erdős Problem 1083

Distinct distances in higher dimensions.

OPEN

*Reference:* [erdosproblems.com/1083](https://www.erdosproblems.com/1083)
-/

open Finset

open scoped Topology Real

namespace Erdos1083

/-- Distinct distances in d-dimensional space -/
@[category research open, AMS 52]
theorem distinct_distances_higher_dim (d n : ℕ) :
    ∀ (S : Finset (EuclideanSpace ℝ (Fin d))),
      S.card = n →
      ∃ (D : Finset ℝ),
        (∀ d_val ∈ D, ∃ x ∈ S, ∃ y ∈ S, dist x y = d_val) ∧
        D.card ≥ sorry := by
  sorry

end Erdos1083
