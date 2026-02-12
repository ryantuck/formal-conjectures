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
# Erdős Problem 1098

Non-commuting graph and complete subgraphs.

PROVED

*Reference:* [erdosproblems.com/1098](https://www.erdosproblems.com/1098)
-/

open Finset

open scoped Topology Real

namespace Erdos1098

variable {G : Type*} [Group G]

/-- English version: Let G be a group and Γ be the non-commuting graph. If Γ contains no infinite complete subgraph, then is there a finite bound on the size of complete subgraphs of Γ? -/
@[category research solved, AMS 20]
theorem non_commuting_graph_cliques (G : Type*) [Group G] :
    answer(True) ↔
    (¬ ∃ (f : ℕ → G), ∀ i j, i ≠ j → f i * f j ≠ f j * f i) →
    ∃ (n : ℕ), ∀ (S : Finset G),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → x * y ≠ y * x) →
      S.card ≤ n := by
  sorry

end Erdos1098
