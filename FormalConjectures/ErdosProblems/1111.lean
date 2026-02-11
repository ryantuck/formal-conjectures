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
# Erdős Problem 1111

Chromatic number and anticomplete vertex sets.

OPEN

*Reference:* [erdosproblems.com/1111](https://www.erdosproblems.com/1111)
-/

open Finset

open scoped Topology Real

namespace Erdos1111

/-- For any t, c >= 1, there exists d such that any graph with
    chi(G) >= d and omega(G) < t contains anticomplete sets A, B
    with chi(G[A]) >= c and chi(G[B]) >= c -/
@[category research open, AMS 05]
theorem chromatic_anticomplete :
    ∀ (t c : ℕ), 1 ≤ t → 1 ≤ c →
      ∃ (d : ℕ), ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
          G.chromaticNumber ≥ d →
          G.cliqueNum < t →
          ∃ (A B : Finset V), Disjoint A B ∧
            (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) ∧
            (G.induce (↑A)).chromaticNumber ≥ c ∧
            (G.induce (↑B)).chromaticNumber ≥ c := by
  sorry

end Erdos1111
