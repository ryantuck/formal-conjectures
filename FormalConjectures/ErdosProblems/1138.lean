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
# Erdős Problem 1138

Asymptotic formula for primes near maximum gaps.

OPEN

*Reference:* [erdosproblems.com/1138](https://www.erdosproblems.com/1138)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1138

/-- Prime counting function -/
noncomputable def π (x : ℝ) : ℕ := sorry

/-- Maximum prime gap below x -/
noncomputable def d (x : ℝ) : ℕ := sorry

/-- Asymptotic formula for primes near maximum gaps -/
@[category research open, AMS 11]
theorem primes_near_max_gaps (C : ℝ) (hC : 1 < C) :
    ∀ (x y : ℝ), x / 2 < y → y < x →
      (π (y + C * d x) - π y : ℝ) / ((C * d x) / Real.log y) → 1 := by
  sorry

end Erdos1138
