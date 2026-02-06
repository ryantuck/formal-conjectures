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
# Erdős Problem 725

Asymptotic formula for number of k×n Latin rectangles.

OPEN

*Reference:* [erdosproblems.com/725](https://www.erdosproblems.com/725)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos725

/-- Number of k×n Latin rectangles -/
noncomputable def latinRectangles (k n : ℕ) : ℕ := sorry

/-- Asymptotic formula for Latin rectangles -/
@[category research open, AMS 05]
theorem latin_rectangles_asymptotic (k : ℕ) :
    ∃ f : ℕ → ℝ, ∀ᶠ (n : ℕ) in Filter.atTop,
      latinRectangles k n ~ f n := by
  sorry

end Erdos725
