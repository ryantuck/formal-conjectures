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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SizeRamsey

/-!
# Erdős Problem 79

*Reference:* [erdosproblems.com/79](https://www.erdosproblems.com/79)
-/

namespace Erdos79

open SimpleGraph

/--
We say $G$ is Ramsey size linear if $R(G,H)\ll m$ for all graphs $H$ with $m$ edges and no
isolated vertices.

Are there infinitely many graphs $G$ which are not Ramsey size linear but such that all of its
subgraphs are?
-/
@[category research solved, AMS 05]
theorem erdos_79 : answer(True) ↔
    Set.Infinite { n | ∃ (G : SimpleGraph (Fin n)),
      ¬ IsRamseySizeLinear G ∧
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), (∃ (f : H ↪g G), True) → IsRamseySizeLinear H } := by
  sorry

end Erdos79