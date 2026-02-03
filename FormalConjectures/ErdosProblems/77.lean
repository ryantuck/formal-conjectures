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
import FormalConjecturesForMathlib.Combinatorics.Ramsey

/-!
# Erdős Problem 77

*Reference:* [erdosproblems.com/77](https://www.erdos.com/77)
-/

namespace Erdos77

open Combinatorics

/--
If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of the
edges of $K_n$ contains a monochromatic copy of $K_k$, then find the value of
$$\lim_{k\to \infty}R(k)^{1/k}.$$ 
-/ 
@[category research open, AMS 05]
theorem erdos_77 : answer(sorry) ↔ ∃ (c : ℝ),
    Filter.Tendsto (fun k ↦ (hypergraphRamsey 2 k : ℝ) ^ (1 / k : ℝ)) Filter.atTop (nhds c) :=
  sorry

end Erdos77
