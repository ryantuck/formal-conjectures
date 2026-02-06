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
# Erdős Problem 1126

Additive functions and measurability.

PROVED

*Reference:* [erdosproblems.com/1126](https://www.erdosproblems.com/1126)
-/

open Finset

open scoped Topology Real

namespace Erdos1126

/-- Additive functions satisfying Cauchy equation almost everywhere extend to everywhere -/
@[category research solved, AMS 26]
theorem additive_function_measurability :
    ∀ (f : ℝ → ℝ),
      (∀ᵐ (x : ℝ), ∀ᵐ (y : ℝ), f (x + y) = f x + f y) →
      ∃ (g : ℝ → ℝ), (∀ x y, g (x + y) = g x + g y) ∧
        (∀ᵐ x, f x = g x) := by
  sorry

end Erdos1126
