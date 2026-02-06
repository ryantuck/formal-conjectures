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
# Erdős Problem 852

Consecutive distinct prime gaps length.

OPEN

*Reference:* [erdosproblems.com/852](https://www.erdosproblems.com/852)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos852

/-- h(x): max length of consecutive distinct prime gaps -/
noncomputable def h (x : ℝ) : ℕ := sorry

/-- Estimate h(x) -/
@[category research open, AMS 11]
theorem consecutive_prime_gaps (answer : Prop) :
    answer ↔ (∃ c : ℝ, c > 0 ∧
      ∀ᶠ (x : ℝ) in Filter.atTop, h x > (Real.log x) ^ c) ∨
      Filter.Tendsto (fun x => h x / Real.log x) Filter.atTop (nhds 0) := by
  sorry

end Erdos852
