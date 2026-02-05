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
# Erdős Problem 614

Define f(n,k) as the minimum number of edges needed in an n-vertex graph such that
every induced subgraph on k+2 vertices has maximum degree at least k. Determine f(n,k).

OPEN

*Reference:* [erdosproblems.com/614](https://www.erdosproblems.com/614)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos614

/-- f(n,k): min edges so every (k+2)-vertex induced subgraph has max degree ≥ k -/
noncomputable def f (n k : ℕ) : ℕ := sorry

/-- Determine f(n,k) -/
@[category research open, AMS 05]
theorem determine_f (n k : ℕ) :
    ∃ m, f n k = m := by
  sorry

end Erdos614
