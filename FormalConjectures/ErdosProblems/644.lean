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
# Erdős Problem 644

Estimate f(k,r) for families of k-sets with intersection properties.

OPEN

*Reference:* [erdosproblems.com/644](https://www.erdosproblems.com/644)
-/

open Finset

open scoped Topology Real

namespace Erdos644

/-- f(k,r) for families of k-sets with intersection properties -/
noncomputable def f (k r : ℕ) : ℕ := sorry

/-- Bounds for f(k,r) -/
@[category research open, AMS 05]
theorem set_family_intersection_property (k r : ℕ) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      c₁ * sorry ≤ f k r ∧ f k r ≤ c₂ * sorry := by
  sorry

end Erdos644
