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
# Erdős Problem 706

Estimate L(r) - chromatic number for distance graphs with r distance values.

OPEN

*Reference:* [erdosproblems.com/706](https://www.erdosproblems.com/706)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos706

/-- L(r): chromatic number for distance graphs with r distance values -/
noncomputable def L (r : ℕ) : ℕ := sorry

/-- Bounds for L(r) -/
@[category research open, AMS 05]
theorem distance_graph_chromatic_estimate (r : ℕ) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      c₁ * (r : ℝ) ≤ L r ∧ L r ≤ c₂ * (r : ℝ) := by
  sorry

end Erdos706
