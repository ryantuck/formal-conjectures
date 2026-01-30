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
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Erdős Problem 24

*Reference:* [erdosproblems.com/24](https://www.erdosproblems.com/24)
-/

namespace Erdos24

open SimpleGraph

/--
Does every triangle-free graph on $5n$ vertices contain at most $n^5$ copies of $C_5$?

The answer is yes, as proved independently by Grzesik [Gr12] and Hatami, Hladky, Král, Norine,
and Razborov [HHKNR13].

[Gr12] A. Grzesik, _On the maximum number of five-cycles in a triangle-free graph_,
J. Combin. Theory Ser. B 102 (2012), 1061-1066.
[HHKNR13] H. Hatami, J. Hladký, D. Král, S. Norine, and A. Razborov,
_On the number of pentagons in triangle-free graphs_, J. Combin. Theory Ser. A 120 (2013), 722-732.
-/
@[category research solved, AMS 05]
theorem erdos_24 : answer(True) ↔ ∀ n : ℕ, ∀ G : SimpleGraph (Fin (5 * n)),
    G.CliqueFree 3 →
    let c5_copies := { s : Finset (Fin (5 * n)) | s.card = 5 ∧ Nonempty ((G.induce s) ≃g (cycleGraph 5)) }
    c5_copies.ncard ≤ n ^ 5 := by
  sorry

end Erdos24
