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

/-!
# Erdős Problem 63

*Reference:* [erdosproblems.com/63](https://www.erdosproblems.com/63)
-/

namespace Erdos63

open SimpleGraph

/--
Does every graph with infinite chromatic number contain a cycle of length $2^n$ for infinitely
many $n$?
-/
@[category research open, AMS 05]
theorem erdos_63 (V : Type*) (G : SimpleGraph V) :
    G.chromaticNumber = ⊤ →
    { n : ℕ | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = 2 ^ n }.Infinite := by
  sorry

end Erdos63
