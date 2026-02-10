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
# Erdős Problem 998

Equidistribution and fractional parts.

PROVED

*Reference:* [erdosproblems.com/998](https://www.erdosproblems.com/998)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos998

/-- Equidistribution condition implies endpoints are fractional parts -/
@[category research solved, AMS 11]
theorem equidistribution_endpoint_condition (α : ℝ) (u v : ℝ) :
    Irrational α →
    0 ≤ u → u < v → v ≤ 1 →
    (∀ m : ℕ, Tendsto (fun N =>
      ((Finset.range N |>.filter (fun k => Int.fract (α * m) ∈ Set.Ioo u v)).card : ℝ) / N)
      atTop (nhds (v - u))) →
    (∃ k : ℕ, u = Int.fract (α * k)) ∧ (∃ k : ℕ, v = Int.fract (α * k)) := by
  sorry

end Erdos998
