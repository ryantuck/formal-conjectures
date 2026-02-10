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
# Erdős Problem 917

Critical graphs and chromatic number edge bounds.

OPEN

*Reference:* [erdosproblems.com/917](https://www.erdosproblems.com/917)
-/

open Finset

open scoped Topology Real

namespace Erdos917

variable {α : Type*}

/-- Delete edges from a graph -/
def deleteEdges (G : SimpleGraph α) (E : Set (α × α)) : SimpleGraph α where
  Adj x y := G.Adj x y ∧ (x, y) ∉ E ∧ (y, x) ∉ E
  symm := fun _ _ h => ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless := fun _ h => G.loopless _ h.1

/-- Critical graphs have many edges -/
@[category research open, AMS 05]
theorem critical_graph_edges (answer : Prop) :
    answer ↔ ∀ k : ℕ, ∃ c : ℝ, c > 0 ∧
      ∀ (G : SimpleGraph α) [Fintype α] [DecidableRel G.Adj],
        G.chromaticNumber = k →
        (∀ e : α × α, G.Adj e.1 e.2 →
          (deleteEdges G {e}).chromaticNumber < k) →
        c * (Fintype.card α : ℝ) ^ 2 ≤ G.edgeFinset.card := by
  sorry

end Erdos917
