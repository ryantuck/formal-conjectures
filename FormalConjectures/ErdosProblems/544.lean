/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 544

Show that R(3,k+1) - R(3,k) → ∞ as k → ∞.
Also determine whether R(3,k+1) - R(3,k) = o(k).

OPEN

*Reference:* [erdosproblems.com/544](https://www.erdosproblems.com/544)
-/

open Filter

namespace Erdos544

/-- Ramsey number R(3,k) -/
noncomputable def R (k : ℕ) : ℕ := sorry

/-- Ramsey number difference grows unbounded -/
@[category research open, AMS 05]
theorem ramsey_diff_unbounded :
    Tendsto (fun k => R (k+1) - R k) atTop atTop := by
  sorry

/-- Is the difference sublinear? -/
@[category research open, AMS 05]
theorem ramsey_diff_sublinear :
    answer(sorry) ↔
      ∀ ε > 0, ∀ᶠ k in atTop,
        (R (k+1) - R k : ℝ) < ε * k := by
  sorry

end Erdos544
