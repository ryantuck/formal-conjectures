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
# Erdős Problem 558

Determine R(K_{s,t};k) for complete bipartite graph K_{s,t}.
Known: R(K_{2,2};k) = (1+o(1))k², R(K_{3,3};k) = (1+o(1))k³

OPEN

*Reference:* [erdosproblems.com/558](https://www.erdosproblems.com/558)
-/

namespace Erdos558

/-- Asymptotics for K_{2,2} -/
@[category research open, AMS 05]
theorem ramsey_k22_asymptotic :
    ∃ c : ℝ, c > 0 ∧ sorry := by
  sorry

/-- Asymptotics for K_{3,3} -/
@[category research open, AMS 05]
theorem ramsey_k33_asymptotic :
    ∃ c : ℝ, c > 0 ∧ sorry := by
  sorry

end Erdos558
