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
# Erdős Problem 78

*Reference:* [erdosproblems.com/78](https://www.erdosproblems.com/78)
-/

namespace Erdos78

open Combinatorics

/--
Let $R(k)$ be the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of the
edges of $K_n$ contains a monochromatic copy of $K_k$.

Give a constructive proof that $R(k)>C^k$ for some constant $C>1$.
-/
@[category research open, AMS 05]
theorem erdos_78 : answer(sorry) ↔ ∃ (C : ℝ), 1 < C ∧
    ∀ (k : ℕ), (hypergraphRamsey 2 k : ℝ) > C ^ k := by
  sorry

end Erdos78
