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
# Erdős Problem 788

Estimate f(n) for Choi conjecture.

OPEN (best bound f(n) ≤ n^(3/5+o(1)))

*Reference:* [erdosproblems.com/788](https://www.erdosproblems.com/788)
-/

open Finset

open scoped Topology Real

namespace Erdos788

/-- f(n) for combinatorial condition -/
noncomputable def f (n : ℕ) : ℕ := sorry

/-- Current best bound -/
@[category research open, AMS 11]
theorem choi_bound :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      f n ≤ (n : ℝ) ^ (3/5 + sorry) := by
  sorry

end Erdos788
