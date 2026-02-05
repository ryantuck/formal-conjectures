/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 545

Let G be a graph with m edges and no isolated vertices. Is R(G) maximized when G
is "as complete as possible"?

If m = C(n,2) + t where 0 ≤ t < n, is R(G) ≤ R(H) where H is K_n with t extra edges
from a new vertex?

OPEN (with known counterexamples for small m)

*Reference:* [erdosproblems.com/545](https://www.erdosproblems.com/545)
-/

namespace Erdos545

/-- Conjecture: complete-like graphs maximize Ramsey number -/
@[category research open, AMS 05]
theorem complete_like_maximizes_ramsey :
    answer(sorry) ↔ sorry := by
  sorry

end Erdos545
