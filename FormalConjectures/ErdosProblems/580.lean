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
# Erdős Problem 580

Let G be a graph on n vertices such that at least n/2 vertices have degree at least n/2.
Must G contain every tree on at most n/2 vertices?

PROVED by Zhao for all sufficiently large n

*Reference:* [erdosproblems.com/580](https://www.erdosproblems.com/580)
-/

open SimpleGraph Finset

open scoped Topology Real

namespace Erdos580

variable {α β : Type*} [Fintype α]

/-- A graph is a tree if it's connected and acyclic -/
def IsTree (G : SimpleGraph α) : Prop := G.Connected ∧ sorry

/-- Half the vertices with degree ≥ n/2 guarantees all small trees -/
@[category research solved, AMS 05]
theorem degree_condition_contains_trees :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (Finset.univ.filter (fun v => G.degree v ≥ n / 2)).card ≥ n / 2 →
      ∀ (T : SimpleGraph β) [Fintype β] (hT : IsTree T) (hcard : Fintype.card β ≤ n / 2),
        ∃ (f : β ↪ Fin n), ∀ i j, T.Adj i j ↔ G.Adj (f i) (f j) := by
  sorry

end Erdos580
