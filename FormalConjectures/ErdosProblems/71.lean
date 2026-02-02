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
# Erdős Problem 71

*Reference:* [erdosproblems.com/71](https://www.erdosproblems.com/71)
-/

namespace Erdos71

open SimpleGraph

/--
Is it true that for every infinite arithmetic progression $P$ which contains even numbers there
is some constant $c=c(P)$ such that every graph with average degree at least $c$ contains a cycle
whose length is in $P$?
-/
@[category research open, AMS 05]
theorem erdos_71 : answer(sorry) ↔ ∀ (a d : ℕ), (∃ n, Even (a + n * d)) →
    ∃ (c : ℝ), ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (2 * (Nat.card G.edgeSet : ℝ) / Fintype.card V) ≥ c →
    ∃ (n : ℕ) (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = a + n * d := by
  sorry

end Erdos71
