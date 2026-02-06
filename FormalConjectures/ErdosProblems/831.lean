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
# Erdős Problem 831

Estimate h(n) for distinct circle radii.

OPEN

*Reference:* [erdosproblems.com/831](https://www.erdosproblems.com/831)
-/

open EuclideanSpace Metric

open scoped Topology Real

namespace Erdos831

/-- h(n): minimum distinct circle radii from n general position points -/
noncomputable def h (n : ℕ) : ℕ := sorry

/-- Estimate h(n) -/
@[category research open, AMS 52]
theorem distinct_circle_radii_general :
    sorry := by
  sorry

end Erdos831
