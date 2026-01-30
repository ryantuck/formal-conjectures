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

/-!
# Erdős Problem 19

*Reference:* [erdosproblems.com/19](https://www.erdosproblems.com/19)
-/

namespace Erdos19

open SimpleGraph
open scoped Classical

/--
The Erdős-Faber-Lovász conjecture:
If $G$ is the union of $n$ copies of $K_n$ which are edge-disjoint, then $\chi(G) = n$.

Kang, Kelly, Kühn, Methuku, and Osthus [KKKMO21] proved this for sufficiently large $n$.
-/
@[category research open, AMS 05]
theorem erdos_19 : answer(sorry) ↔ ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (∃ (K : Fin n → Set V),
      (∀ i, G.IsClique (K i) ∧ Set.ncard (K i) = n) ∧
      (∀ i j, i ≠ j → Disjoint (Set.image2 (fun u v => Sym2.mk (u, v)) (K i) (K i) \ {Sym2.mk (v, v) | v : V})
                               (Set.image2 (fun u v => Sym2.mk (u, v)) (K j) (K j) \ {Sym2.mk (v, v) | v : V})) ∧
      G.edgeSet = ⋃ i, (Set.image2 (fun u v => Sym2.mk (u, v)) (K i) (K i)) \ {Sym2.mk (v, v) | v : V}) →
    G.chromaticNumber = n := by
  sorry

end Erdos19
