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
# Erdős Problem 907

Function decomposition with continuous differences.

PROVED

*Reference:* [erdosproblems.com/907](https://www.erdosproblems.com/907)
-/

open scoped Topology Real

namespace Erdos907

/-- Function with continuous differences decomposes as g + h -/
@[category research solved, AMS 41]
theorem continuous_diff_decomposition :
    ∀ (f : ℝ → ℝ),
      (∀ x y : ℝ, Continuous (fun z => f (x + z) - f z)) →
      ∃ (g h : ℝ → ℝ),
        (∀ x : ℝ, f x = g x + h x) ∧
        Continuous g ∧
        (∀ x y : ℝ, h (x + y) = h x + h y) := by
  sorry

end Erdos907
