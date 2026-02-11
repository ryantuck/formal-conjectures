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
# Erdős Problem 1125

Convexity and monotonicity.

PROVED

*Reference:* [erdosproblems.com/1125](https://www.erdosproblems.com/1125)
-/

open Finset

open scoped Real

namespace Erdos1125

/-- Let f : R -> R satisfy 2f(x) <= f(x+h) + f(x+2h) for every x in R and h > 0.
    Then f is monotonic. Proved by Kemperman (measurable case) and Laczkovich (1984, general case). -/
@[category research solved, AMS 26]
theorem convexity_monotonicity :
    ∀ (f : ℝ → ℝ),
      (∀ x : ℝ, ∀ h : ℝ, 0 < h → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
      Monotone f ∨ Antitone f := by
  sorry

end Erdos1125
