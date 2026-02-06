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
# Erdős Problem 721

Bounds for van der Waerden number W(3,k).

SOLVED

*Reference:* [erdosproblems.com/721](https://www.erdosproblems.com/721)
-/

open Finset

open scoped Topology Real

namespace Erdos721

/-- Van der Waerden number W(3,k) -/
noncomputable def W (k : ℕ) : ℕ := sorry

/-- Lower bound for W(3,k) -/
@[category research solved, AMS 05]
theorem van_der_waerden_lower_bound :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (k : ℕ) in Filter.atTop,
        W k ≥ Real.exp (c * (Real.log k) ^ 2 / Real.log (Real.log k)) := by
  sorry

/-- Upper bound W(3,k) < exp(k^c) for c < 1 -/
@[category research solved, AMS 05]
theorem van_der_waerden_upper_bound :
    ∃ c : ℝ, c < 1 ∧
      ∀ᶠ (k : ℕ) in Filter.atTop,
        (W k : ℝ) < Real.exp ((k : ℝ) ^ c) := by
  sorry

end Erdos721
