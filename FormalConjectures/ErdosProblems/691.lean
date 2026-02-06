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
# Erdős Problem 691

Find necessary and sufficient condition on A for M_A (multiples of A) to have density 1.

OPEN

*Reference:* [erdosproblems.com/691](https://www.erdosproblems.com/691)
-/

open scoped Topology Real

namespace Erdos691

/-- M_A: set of integers with at least one divisor from A -/
def M_A (A : Set ℕ) : Set ℕ := sorry

/-- Density of a set -/
noncomputable def density (S : Set ℕ) : ℝ := sorry

/-- Characterize sets A where M_A has density 1 -/
@[category research open, AMS 11]
theorem multiples_density_one_characterization :
    ∃ P : Set ℕ → Prop, ∀ A : Set ℕ,
      density (M_A A) = 1 ↔ P A := by
  sorry

end Erdos691
