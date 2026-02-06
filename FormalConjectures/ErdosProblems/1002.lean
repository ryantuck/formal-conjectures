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
# Erdős Problem 1002

Asymptotic distribution of fractional part sums.

OPEN

*Reference:* [erdosproblems.com/1002](https://www.erdosproblems.com/1002)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1002

/-- Function f(α,n) for fractional part sums -/
noncomputable def f (α : ℝ) (n : ℕ) : ℝ :=
  (1 / Real.log n) * ∑ k in Finset.range n, (1/2 - {α * k})

/-- Asymptotic distribution function exists -/
@[category research open, AMS 11]
theorem fractional_sum_distribution (answer : Prop) :
    answer ↔ ∃ (g : ℝ → ℝ),
      ∀ x : ℝ, Tendsto (fun α => volume {β ∈ Set.Icc 0 1 |
        ∃ᶠ n in atTop, f β n < x})
        sorry (nhds (g x)) := by
  sorry

end Erdos1002
