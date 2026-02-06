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
# Erdős Problem 908

Measurable function decomposition.

PROVED

*Reference:* [erdosproblems.com/908](https://www.erdosproblems.com/908)
-/

open scoped Topology Real

namespace Erdos908

/-- Measurable function decomposes as g + h + r -/
@[category research solved, AMS 41]
theorem measurable_decomposition :
    ∀ (f : ℝ → ℝ),
      Measurable f →
      ∃ (g h r : ℝ → ℝ),
        (∀ x : ℝ, f x = g x + h x + r x) ∧
        Continuous g ∧
        (∀ x y : ℝ, h (x + y) = h x + h y) ∧
        (∃ T : ℝ, T > 0 ∧ ∀ x : ℝ, r (x + T) = r x) := by
  sorry

end Erdos908
