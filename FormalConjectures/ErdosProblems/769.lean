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
# Erdős Problem 769

Cube decomposition into homothetic cubes.

OPEN

*Reference:* [erdosproblems.com/769](https://www.erdosproblems.com/769)
-/

open Finset

open scoped Topology Real

namespace Erdos769

/-- c(n): minimal value for cube decomposition -/
noncomputable def c (n : ℕ) : ℕ := sorry

/-- Conjecture: c(n) ≫ n^n -/
@[category research open, AMS 52]
theorem cube_decomposition_bound (answer : Prop) :
    answer ↔ ∃ C : ℝ, C > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop, c n ≥ C * (n : ℝ) ^ n := by
  sorry

end Erdos769
