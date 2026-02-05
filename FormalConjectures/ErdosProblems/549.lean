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
# Erdős Problem 549

If T is a bipartite tree with k vertices in one class and 2k in the other,
is R(T) = 4k - 1?

DISPROVED: Norin-Sun-Zhao showed R(T) ≥ (4.2-o(1))k for specific T.

*Reference:* [erdosproblems.com/549](https://www.erdosproblems.com/549)
-/

namespace Erdos549

/-- Disproof: bipartite tree Ramsey number can exceed 4k-1 -/
@[category research solved, AMS 05]
theorem bipartite_tree_counterexample :
    answer(False) ↔ sorry := by
  sorry

end Erdos549
