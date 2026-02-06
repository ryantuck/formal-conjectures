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
# Erdős Problem 712

Determine limit of ex_r(n,K_k^r) / C(n,r) for k>r>2.

OPEN ($500 reward)

*Reference:* [erdosproblems.com/712](https://www.erdosproblems.com/712)
-/

open Finset Nat

open scoped Topology Real

namespace Erdos712

/-- Turán number for r-uniform hypergraphs -/
noncomputable def ex_r (n k r : ℕ) : ℕ := sorry

/-- Determine the limit ex_r(n,K_k^r) / C(n,r) -/
@[category research open, AMS 05]
theorem hypergraph_turan_limit (k r : ℕ) (hk : k > r) (hr : r > 2) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n => (ex_r n k r : ℝ) / Nat.choose n r)
      Filter.atTop (nhds L) := by
  sorry

end Erdos712
