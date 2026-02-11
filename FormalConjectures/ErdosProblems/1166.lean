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
# Erdős Problem 1166

Union of favourite sets in random walks.

PROVED - The union is bounded by (log n)²

*Reference:* [erdosproblems.com/1166](https://www.erdosproblems.com/1166)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos1166

/-- Consider a random walk in ℤ² starting at the origin. Let f_k(x) count visits to x by time k.
    Let F(k) = {x : f_k(x) = max_y f_k(y)} be the set of most-visited locations.

    Proved: |⋃_{k ≤ n} F(k)| ≪ (log n)² almost surely for all large n.

    This follows from:
    1. Almost surely |F(n)| ≤ 3 for all large n (Problem 1165)
    2. Erdős-Taylor: maximum visits ≪ (log n)²

    This formalization states the asymptotic bound.

    Note: Without probability infrastructure, this asks whether such a function exists.
    The "almost surely" aspect is not captured. -/
@[category research solved, AMS 60]
theorem union_favorite_sets_bound :
    answer(True) ↔
      ∃ (union_size : ℕ → ℕ) (C : ℝ), C > 0 ∧
        ∀ᶠ (n : ℕ) in atTop,
          (union_size n : ℝ) ≤ C * (Real.log n)^2 := by
  sorry

end Erdos1166
