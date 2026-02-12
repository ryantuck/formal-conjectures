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
# Erdős Problem 1017

Clique partition of graphs.

OPEN

STATUS: OPEN

*Reference:* [erdosproblems.com/1017](https://www.erdosproblems.com/1017)
-/

open Finset Filter

open scoped Topology Real

namespace Erdos1017

variable {α : Type*}

/--
English version:  Minimum clique partition size -/
noncomputable def f (n k : ℕ) : ℕ := sorry

/--
English version:  -/
@[category research open, AMS 05]
theorem clique_partition_estimate (answer(sorry) : ℕ → ℕ → ℝ) :
    ∀ k : ℕ,
      Filter.Tendsto (fun (n : ℕ) => (f n k : ℝ) / answer(sorry) n k) Filter.atTop (nhds 1) := by
  sorry

end Erdos1017
