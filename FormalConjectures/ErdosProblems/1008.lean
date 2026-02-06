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
# Erdős Problem 1008

C₄-free subgraph conjecture.

PROVED

*Reference:* [erdosproblems.com/1008](https://www.erdosproblems.com/1008)
-/

open Finset

open scoped Topology Real

namespace Erdos1008

variable {α : Type*}

/-- Every graph contains C₄-free subgraph with many edges -/
@[category research solved, AMS 05]
theorem c4_free_subgraph (m : ℕ) :
    ∀ (G : SimpleGraph α) [Fintype α],
      G.edgeFinset.card = m →
      ∃ (H : SimpleGraph α),
        H ≤ G ∧ H.CliqueFree 4 ∧
        ∃ (c : ℝ), 0 < c ∧ c * m ^ (2/3 : ℝ) ≤ H.edgeFinset.card := by
  sorry

end Erdos1008
