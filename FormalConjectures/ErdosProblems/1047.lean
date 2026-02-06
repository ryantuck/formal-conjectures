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
# Erdős Problem 1047

Convexity of level set components.

DISPROVED

*Reference:* [erdosproblems.com/1047](https://www.erdosproblems.com/1047)
-/

open Finset

open scoped Topology Real

namespace Erdos1047

/-- Level set components need not be convex -/
@[category research open, AMS 30]
theorem convexity_of_components (answer : Prop) :
    answer ↔ ∀ (f : Polynomial ℂ) (c : ℝ),
      f.Monic →
      0 < c →
      sorry := by
  sorry

end Erdos1047
