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
# Erdős Problem 974

Roots of unity and power sums.

PROVED

*Reference:* [erdosproblems.com/974](https://www.erdosproblems.com/974)
-/

open Finset

open scoped Topology Real

namespace Erdos974

/-- Characterization via consecutive zero power sums -/
@[category research solved, AMS 12]
theorem roots_unity_characterization (n : ℕ) :
    ∀ (z : Fin n → ℂ),
      z 0 = 1 →
      (∃ᶠ m in Filter.atTop, ∀ k : Fin (n - 1), ∑ i : Fin n, (z i) ^ (m + k) = 0) →
      ∃ (ζ : ℂ), ζ ^ n = 1 ∧
        ∀ i : Fin n, ∃ j : Fin n, z i = ζ ^ j.val := by
  sorry

end Erdos974
