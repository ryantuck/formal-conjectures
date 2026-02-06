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
# Erdős Problem 781

Monochromatic descending wave.

DISPROVED

*Reference:* [erdosproblems.com/781](https://www.erdosproblems.com/781)
-/

open Finset

open scoped Topology Real

namespace Erdos781

/-- f(k): minimal n for monochromatic descending wave -/
noncomputable def f (k : ℕ) : ℕ := sorry

/-- Disproved: f(k) = k² - k + 1 -/
@[category research solved, AMS 05]
theorem descending_wave_bound :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (k : ℕ) in Filter.atTop,
        f k ≥ c * (k : ℝ) ^ 3 := by
  sorry

end Erdos781
