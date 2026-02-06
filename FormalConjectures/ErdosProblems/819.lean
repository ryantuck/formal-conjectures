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
# Erdős Problem 819

Maximal f(N) for subset property.

OPEN (bounds (3/8-o(1))N ≤ f(N) ≤ (1/2+o(1))N)

*Reference:* [erdosproblems.com/819](https://www.erdosproblems.com/819)
-/

open Finset

open scoped Topology Real

namespace Erdos819

/-- f(N): maximal value for subset property -/
noncomputable def f (N : ℕ) : ℕ := sorry

/-- Current bounds for f(N) -/
@[category research open, AMS 11]
theorem subset_property_bounds :
    ∀ᶠ (N : ℕ) in Filter.atTop,
      (3/8 - sorry) * N ≤ f N ∧
      f N ≤ (1/2 + sorry) * N := by
  sorry

end Erdos819
