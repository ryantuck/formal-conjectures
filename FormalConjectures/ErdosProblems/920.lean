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
# Erdős Problem 920

Chromatic number of K_k-free graphs.

OPEN

*Reference:* [erdosproblems.com/920](https://www.erdosproblems.com/920)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos920

variable {α : Type*}

/-- Minimum vertices for K_k-free graph with chromatic number r -/
noncomputable def h (k r : ℕ) : ℕ := sorry

/-- Asymptotic formula for h(k,r) -/
@[category research open, AMS 05]
theorem chromatic_clique_free_asymptotic (k : ℕ) (answer : Prop) :
    answer ↔ ∃ (f : ℕ → ℝ),
      Tendsto (fun r => (h k (r + 1) : ℝ) / h k r) atTop (nhds 1) := by
  sorry

end Erdos920
