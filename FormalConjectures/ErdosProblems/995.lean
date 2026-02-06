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
# Erdős Problem 995

Growth estimation of lacunary sequence sums.

OPEN

*Reference:* [erdosproblems.com/995](https://www.erdosproblems.com/995)
-/

open Finset Filter MeasureTheory

open scoped Topology Real

namespace Erdos995

/-- Growth of lacunary sequence sums -/
@[category research open, AMS 11]
theorem lacunary_sum_growth (answer : Prop) :
    answer ↔ ∀ (n : ℕ → ℕ), StrictMono n →
      (∀ k : ℕ, (n (k + 1) : ℝ) / n k ≥ 1 + sorry) →
      ∀ (f : ℝ → ℝ), Measurable f →
        ∫ x in Set.Icc 0 1, f x ^ 2 < ∞ →
        ∀ᵐ α, |(Finset.range sorry |>.sum (fun k => f {α * n k}))| =
          o(fun N => N * Real.sqrt (Real.log (Real.log N))) := by
  sorry

end Erdos995
