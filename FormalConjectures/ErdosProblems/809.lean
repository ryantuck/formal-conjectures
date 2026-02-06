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
# Erdős Problem 809

Minimal colors for odd cycle rainbow.

OPEN (conjecture F_k(n) ~ n²/8)

*Reference:* [erdosproblems.com/809](https://www.erdosproblems.com/809)
-/

open Finset

open scoped Topology Real

namespace Erdos809

/-- F_k(n): minimal colors for C_(2k+1) rainbow -/
noncomputable def F_k (k n : ℕ) : ℕ := sorry

/-- Conjecture: F_k(n) ~ n²/8 -/
@[category research open, AMS 05]
theorem odd_cycle_rainbow_colors (k : ℕ) (answer : Prop) :
    answer ↔ Filter.Tendsto
      (fun n => (F_k k n : ℝ) / ((n : ℝ) ^ 2 / 8))
      Filter.atTop (nhds 1) := by
  sorry

end Erdos809
