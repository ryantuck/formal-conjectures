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
# Erdős Problem 987

Exponential sum bounds.

OPEN

*Reference:* [erdosproblems.com/987](https://www.erdosproblems.com/987)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos987

/-- Exponential sum growth -/
@[category research open, AMS 11]
theorem exponential_sum_growth (seq : ℕ → ℝ) (answer : Prop) :
    answer ↔ (∀ i : ℕ, seq i ∈ Set.Ioo 0 1) →
      let A := fun k => limsup (fun n => |(Finset.range n).sum (fun j => Complex.exp (2 * Real.pi * Complex.I * k * seq j))|) atTop
      (limsup A atTop = ⊤) ∧
      (∃ (seq' : ℕ → ℝ), (∀ i, seq' i ∈ Set.Ioo 0 1) ∧
        let A' := fun k => limsup (fun n => |(Finset.range n).sum (fun j => Complex.exp (2 * Real.pi * Complex.I * k * seq' j))|) atTop
        A' = o(id)) := by
  sorry

end Erdos987
