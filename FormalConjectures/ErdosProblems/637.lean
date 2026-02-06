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
# Erdős Problem 637

Does every graph contain an induced subgraph with ≫ n^(1/2) distinct degrees?

PROVED by Bukh and Sudakov (2007); improved to n^(2/3)

*Reference:* [erdosproblems.com/637](https://www.erdosproblems.com/637)
-/

open SimpleGraph Finset

open scoped Topology Real

namespace Erdos637

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every graph contains induced subgraph with ≫ n^(2/3) distinct degrees -/
@[category research solved, AMS 05]
theorem induced_subgraph_distinct_degrees :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ (S : Finset (Fin n)),
          (Finset.univ.image (fun v => (S.filter (fun w => G.Adj v w ∧ v ∈ S ∧ w ∈ S)).card)).card
            ≥ Nat.floor (c * (n : ℝ) ^ (2/3)) := by
  sorry

end Erdos637
