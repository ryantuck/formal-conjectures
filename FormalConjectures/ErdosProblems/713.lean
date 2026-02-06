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
# Erdős Problem 713

Does ex(n;G) ~ cn^α for bipartite G? Must α be rational?

OPEN ($500 reward)

*Reference:* [erdosproblems.com/713](https://www.erdosproblems.com/713)
-/

open Finset

open scoped Topology Real

namespace Erdos713

variable {α : Type*}

/-- Turán number for forbidden subgraph -/
noncomputable def ex (n : ℕ) (G : SimpleGraph α) : ℕ := sorry

/-- Power law for bipartite Turán numbers -/
@[category research open, AMS 05]
theorem bipartite_turan_power_law (answer : Prop) :
    answer ↔ ∀ (G : SimpleGraph α), G.IsBipartite →
      ∃ (α : ℝ) (c : ℝ), α ∈ Set.Ioo 1 2 ∧ c > 0 ∧
        ∀ᶠ (n : ℕ) in Filter.atTop, ex n G ~ fun n => c * (n : ℝ) ^ α := by
  sorry

end Erdos713
