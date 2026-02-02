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

/-!
# Erdős Problem 60

*Reference:* [erdosproblems.com/60](https://www.erdosproblems.com/60)
-/

namespace Erdos60

open SimpleGraph

/--
$\mathrm{ex}(n;C_4)$ is the maximum number of edges in a graph on $n$ vertices which does
not contain $C_4$ as a subgraph.
-/
noncomputable def turanNumberC4 (n : ℕ) : ℕ :=
  sSup { k | ∃ (H : SimpleGraph (Fin n)), Nat.card H.edgeSet = k ∧ ¬ ∃ (f : cycleGraph 4 ↪g H), True }

/--
Does every graph on $n$ vertices with $>\mathrm{ex}(n;C_4)$ edges contain $\gg n^{1/2}$ many
copies of $C_4$?
-/
@[category research open, AMS 05]
theorem erdos_60 : answer(sorry) ↔ ∃ (c : ℝ), 0 < c → ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    ∀ (G : SimpleGraph (Fin n)), Nat.card G.edgeSet > turanNumberC4 n →
    let copiesC4 := { f : cycleGraph 4 ↪g G | True }
    (Set.ncard copiesC4 : ℝ) ≥ c * n ^ (1 / 2 : ℝ) := by
  sorry

end Erdos60
