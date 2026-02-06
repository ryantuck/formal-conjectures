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
# Erdős Problem 715

Every 4-regular graph contains a 3-regular subgraph.

PROVED

*Reference:* [erdosproblems.com/715](https://www.erdosproblems.com/715)
-/

open Finset

open scoped Topology Real

namespace Erdos715

variable {α : Type*}

/-- Every r-regular graph with r≥4 contains a 3-regular subgraph -/
@[category research solved, AMS 05]
theorem regular_graph_contains_three_regular (r : ℕ) (hr : r ≥ 4) :
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj],
      G.IsRegularOfDegree r →
      ∃ (S : Set α), ∃ (H : SimpleGraph S),
        H.IsRegularOfDegree 3 := by
  sorry

end Erdos715
