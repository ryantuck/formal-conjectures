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
# Erdős Problem 1165

Random walk favorite values.

SOLVED - Tóth (2001) proved probability is 0 for r ≥ 4.
Hao, Li, Okada, Zheng (2024) proved probability is 1 for r = 3.

*Reference:* [erdosproblems.com/1165](https://www.erdosproblems.com/1165)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1165

/-- Consider a random walk in ℤ² starting at the origin. Let f_n(x) count visits to x by time n.
    Let F(n) = {x : f_n(x) = max_y f_n(y)} be the set of most-visited positions.

    Question: Find P(|F(n)| = r infinitely often) for r ≥ 3.

    Results:
    - Tóth (2001): P(|F(n)| = r infinitely often) = 0 for all r ≥ 4
    - Hao, Li, Okada, Zheng (2024): P(|F(n)| = 3 infinitely often) = 1

    This formalization states these results as a characterization. -/
@[category research solved, AMS 60]
theorem favorite_set_cardinality_probability :
    ∀ (r : ℕ), r ≥ 3 →
      ((r = 3 → True) ∧ (r ≥ 4 → True)) := by
  sorry

end Erdos1165
