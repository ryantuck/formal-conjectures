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
# Erdős Problem 582

Does there exist a graph G which contains no K_4 yet any 2-coloring of its edges
produces a monochromatic K_3? (Folkman number)

PROVED

*Reference:* [erdosproblems.com/582](https://www.erdosproblems.com/582)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos582

variable {α : Type*}

/-- Folkman graph exists: K_4-free but forces monochromatic triangles -/
@[category research solved, AMS 05]
theorem folkman_graph_exists :
    ∃ (G : SimpleGraph ℕ),
      (∀ (f : Fin 4 ↪ ℕ), ¬ ∀ i j, i ≠ j → G.Adj (f i) (f j)) ∧
      (∀ (coloring : ∀ v w, G.Adj v w → Fin 2),
        ∃ (a b c : ℕ), G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
          coloring a b sorry = coloring b c sorry ∧
          coloring b c sorry = coloring c a sorry) := by
  sorry

end Erdos582
