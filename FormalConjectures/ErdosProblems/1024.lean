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
# Erdős Problem 1024

Independent sets in 3-uniform hypergraphs.

SOLVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1024](https://www.erdosproblems.com/1024)
-/

open Finset

open scoped Topology Real

namespace Erdos1024

variable {α : Type*}

/--
English version:  Minimum independent set size in 3-uniform linear hypergraph -/
noncomputable def f (n : ℕ) : ℕ := sorry

/--
English version:  -/
@[category research solved, AMS 05]
theorem hypergraph_independent_set :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (n : ℕ) (H : Finset (Finset α)) [Fintype α],
        (∀ e ∈ H, e.card = 3) →
        f n ≤ sorry := by
  sorry

end Erdos1024
