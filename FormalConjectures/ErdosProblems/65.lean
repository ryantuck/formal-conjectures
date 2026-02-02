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
# Erdős Problem 65

*Reference:* [erdosproblems.com/65](https://www.erdosproblems.com/65)
-/

namespace Erdos65

open SimpleGraph Classical

/--
Let $G$ be a graph with $n$ vertices and $kn$ edges, and $a_1<a_2<\cdots $ be the lengths of
cycles in $G$. Is it true that
$$\sum\frac{1}{a_i}\gg \log k?$$
Is the sum $\sum\frac{1}{a_i}$ minimised when $G$ is a complete bipartite graph?
-/
@[category research open, AMS 05]
theorem erdos_65 : answer(sorry) ↔ ∃ (c : ℝ), 0 < c ∧
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    let n := Fintype.card V
    let m := Nat.card G.edgeSet
    let k := (m : ℝ) / n
    let cycleLengths := { l : ℕ | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = l }
    n > 0 → k > 1 →
    (∑ l ∈ Finset.Icc 1 n, if l ∈ cycleLengths then (1 : ℝ) / l else 0) ≥ c * Real.log k := by
  sorry

end Erdos65