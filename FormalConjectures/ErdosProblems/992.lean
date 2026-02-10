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
# Erdős Problem 992

Discrepancy of integer sequences.

DISPROVED

*Reference:* [erdosproblems.com/992](https://www.erdosproblems.com/992)
-/

open Finset Filter MeasureTheory

open scoped Topology Real

namespace Erdos992

/-- Disproved: discrepancy bound for integer sequences -/
@[category research solved, AMS 11]
theorem not_discrepancy_bound :
    ¬ ∀ (x : ℕ → ℕ), StrictMono x →
      ∀ α ∈ Set.Icc (0 : ℝ) 1,
        let D := fun N => ((((Finset.range N).sum (fun k => if Int.fract ((x k : ℝ) * α) < α then (1 : ℝ) else 0) - α * N) : ℝ).natAbs : ℝ)
        ∃ ε > 0, ∀ᶠ N in atTop, D N ≤ (N : ℝ) ^ (1/2) * (Real.log N) ^ ε := by
  sorry

end Erdos992
