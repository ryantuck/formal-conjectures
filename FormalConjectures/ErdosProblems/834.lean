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
# Erdős Problem 834

3-critical 3-uniform hypergraph degree.

SOLVED

*Reference:* [erdosproblems.com/834](https://www.erdosproblems.com/834)
-/

open Finset Classical

open scoped Topology Real

namespace Erdos834

variable {α : Type*}

/-- 3-critical hypergraph -/
def IsCritical3 (H : Finset (Finset α)) : Prop := sorry

/-- 3-critical with every vertex degree ≥ 7 -/
@[category research solved, AMS 05]
theorem critical_three_degree_seven (answer : Prop) :
    answer ↔ ∃ (H : Finset (Finset α)),
      (∀ e ∈ H, e.card = 3) ∧
      IsCritical3 H ∧
      ∀ (v : α), (H.filter (fun e => v ∈ e)).card ≥ 7 := by
  sorry

end Erdos834
