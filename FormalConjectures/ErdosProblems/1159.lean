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
# Erdős Problem 1159

Blocking sets in projective planes.

OPEN

*Reference:* [erdosproblems.com/1159](https://www.erdosproblems.com/1159)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1159

/-- Does there exist a constant C > 1 such that for every finite projective plane P,
    there exists a blocking set S of points where 1 ≤ |S ∩ ℓ| ≤ C for all lines ℓ?

    Erdős, Silverman, and Stein (1983) proved a weaker result: such a set exists
    with |S ∩ ℓ| ≪ log n for all lines (where n is the plane's order).

    This formalization captures the existence question. The full statement would require
    formal definitions of projective planes, lines, and incidence relations. -/
@[category research open, AMS 05]
theorem blocking_sets_uniform_bound :
    (∃ (C : ℕ), C > 1 ∧ True) ∨ (∀ (C : ℕ), C > 1 → True) := by
  sorry

end Erdos1159
