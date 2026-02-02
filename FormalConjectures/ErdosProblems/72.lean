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
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Erdős Problem 72

*Reference:* [erdosproblems.com/72](https://www.erdosproblems.com/72)
-/

namespace Erdos72

open SimpleGraph

/--
Is there a set $A\subset \mathbb{N}$ of density $0$ and a constant $c>0$ such that every graph
on sufficiently many vertices with average degree $\geq c$ contains a cycle whose length is in $A$?
-/
@[category research open, AMS 05]
theorem erdos_72 : answer(sorry) ↔ ∃ (A : Set ℕ), Set.HasDensity A 0 ∧
    ∃ (c : ℝ), 0 < c ∧ ∃ (N₀ : ℕ), ∀ (V : Type*) [Fintype V], Fintype.card V ≥ N₀ →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    (2 * (Nat.card G.edgeSet : ℝ) / Fintype.card V) ≥ c →
    ∃ (l : ℕ), l ∈ A ∧ ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = l := by
  sorry

end Erdos72
