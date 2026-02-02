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
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 58

*Reference:* [erdosproblems.com/58](https://www.erdosproblems.com/58)
-/

namespace Erdos58

open SimpleGraph

/--
If $G$ is a graph which contains odd cycles of $\le k$ different lengths then $\chi(G)\leq 2k+2$,
with equality if and only if $G$ contains $K_{2k+2}$.
-/
@[category research solved, AMS 05]
theorem erdos_58 (V : Type*) (G : SimpleGraph V) (k : ℕ) :
    let oddCycleLengths := { n | Odd n ∧ ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = n }
    Set.ncard oddCycleLengths ≤ k →
    G.chromaticNumber ≤ 2 * k + 2 ∧
    (G.chromaticNumber = 2 * k + 2 ↔ ∃ (s : Finset V), G.IsNClique (2 * k + 2) s) := by
  sorry

end Erdos58
