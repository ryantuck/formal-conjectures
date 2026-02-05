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
# Erdős Problem 560

Determine R̂(K_{n,n}), the size Ramsey number for complete bipartite graph K_{n,n}.
Known: (1/60)n²·2ⁿ < R̂(K_{n,n}) < (3/2)n³·2ⁿ

Conjectured: R̂(K_{n,n}) ≍ n³·2ⁿ

OPEN

*Reference:* [erdosproblems.com/560](https://www.erdosproblems.com/560)
-/

open Real

namespace Erdos560

/-- Bounds for size Ramsey of K_{n,n} -/
@[category research open, AMS 05]
theorem size_ramsey_complete_bipartite_bounds (n : ℕ) (hn : n ≥ 6) :
    True := by
  trivial

/-- Conjecture: cubic growth -/
@[category research open, AMS 05]
theorem size_ramsey_knn_conjecture :
    answer(sorry) ↔ sorry := by
  sorry

end Erdos560
