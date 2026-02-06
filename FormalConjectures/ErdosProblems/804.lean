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
# Erdős Problem 804

Estimate f(m,n) for induced subgraph independence.

DISPROVED

*Reference:* [erdosproblems.com/804](https://www.erdosproblems.com/804)
-/

open Finset

open scoped Topology Real

namespace Erdos804

/-- Independence number -/
noncomputable def independenceNumber (G : SimpleGraph α) : ℕ := sorry

/-- f(m,n) estimate -/
noncomputable def f (m n : ℕ) : ℕ := sorry

/-- Disproved conjecture -/
@[category research solved, AMS 05]
theorem not_induced_independence_bound :
    sorry := by
  sorry

end Erdos804
