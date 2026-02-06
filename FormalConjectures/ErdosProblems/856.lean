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
# Erdős Problem 856

fₖ(N) for identical pairwise LCMs.

OPEN

*Reference:* [erdosproblems.com/856](https://www.erdosproblems.com/856)
-/

open Finset Nat

open scoped Topology Real BigOperators

namespace Erdos856

/-- fₖ(N): max reciprocal sum with no k-subset having identical LCMs -/
noncomputable def f_k (k N : ℕ) : ℝ := sorry

/-- Estimate fₖ(N) -/
@[category research open, AMS 11]
theorem identical_lcm_reciprocals :
    sorry := by
  sorry

end Erdos856
