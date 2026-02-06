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
# Erdős Problem 1011

Triangle containment with chromatic number constraints.

OPEN

*Reference:* [erdosproblems.com/1011](https://www.erdosproblems.com/1011)
-/

open Finset

open scoped Topology Real

namespace Erdos1011

variable {α : Type*}

/-- Minimum edges for triangle in graph with chromatic number ≥ r -/
noncomputable def f (r n : ℕ) : ℕ := sorry

/-- Formula for f_r(n) -/
@[category research open, AMS 05]
theorem triangle_chromatic_threshold (r : ℕ) (answer : ℕ → ℕ) :
    ∃ (g : ℕ → ℕ),
      ∀ n : ℕ, f r n = Nat.floor ((n - g r) ^ 2 / 4) + sorry := by
  sorry

end Erdos1011
