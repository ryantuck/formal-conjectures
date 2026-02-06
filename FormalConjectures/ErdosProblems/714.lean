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
# Erdős Problem 714

Is ex(n; K_{r,r}) ≫ n^{2-1/r}?

OPEN

*Reference:* [erdosproblems.com/714](https://www.erdosproblems.com/714)
-/

open Finset

open scoped Topology Real

namespace Erdos714

variable {α β : Type*}

/-- Turán number for forbidden subgraph -/
noncomputable def ex (n : ℕ) (G : SimpleGraph α) : ℕ := sorry

/-- Complete bipartite graph K_{r,r} -/
def completebipartiteGraph (r : ℕ) : SimpleGraph (Fin r ⊕ Fin r) := sorry

/-- Lower bound for ex(n; K_{r,r}) -/
@[category research open, AMS 05]
theorem complete_bipartite_turan_lower_bound (r : ℕ) (answer : Prop) :
    answer ↔ ∃ c : ℝ, c > 0 ∧
      ∀ᶠ (n : ℕ) in Filter.atTop,
        ex n (completebipartiteGraph r) ≥ c * (n : ℝ) ^ (2 - 1/r) := by
  sorry

end Erdos714
