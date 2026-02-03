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
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Erdős Problem 110

*Reference:* [erdosproblems.com/110](https://www.erdosproblems.com/110)
-/

namespace Erdos110

open SimpleGraph Classical

/--
Is there some $F(n)$ such that every graph with chromatic number $\aleph_1$ has, for all large
$n$, a subgraph with chromatic number $n$ on at most $F(n)$ vertices?
-/

-- We model graphs with arbitrary vertex types.
-- "every graph with chromatic number \aleph_1" implies infinite graphs.

def HasChromaticNumber {V : Type*} (G : SimpleGraph V) (k : Cardinal) : Prop :=
  G.chromaticNumber = k

def SubgraphWithChromNum {V : Type*} (G : SimpleGraph V) (n : ℕ) (size : ℕ) : Prop :=
  ∃ (S : Set V), S.ncard ≤ size ∧ (G.induce S).chromaticNumber = n

@[category research open, AMS 05]
theorem erdos_110 : answer(sorry) ↔
  ∃ (F : ℕ → ℕ), ∀ (V : Type) (G : SimpleGraph V),
    HasChromaticNumber G (Cardinal.aleph 1) →
    ∀ᶠ n in Filter.atTop, SubgraphWithChromNum G n (F n) := by
  sorry

end Erdos110