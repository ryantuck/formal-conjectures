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
# Erdős Problem 57

*Reference:* [erdosproblems.com/57](https://www.erdosproblems.com/57)
-/

namespace Erdos57

open SimpleGraph

/--
If $G$ is a graph with infinite chromatic number and $a_1<a_2<\cdots $ are lengths of the odd
cycles of $G$ then $\sum \frac{1}{a_i}=\infty$.
-/
@[category research open, AMS 05]
theorem erdos_57 (V : Type*) (G : SimpleGraph V) :
    G.chromaticNumber = ⊤ →
    let oddCycleLengths := { n | Odd n ∧ ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = n }
    ¬ Summable (fun (n : oddCycleLengths) ↦ (1 : ℝ) / n) := by
  sorry

end Erdos57
