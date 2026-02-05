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
# Erdős Problem 610

For a graph G on n vertices, let τ(G) denote the clique transversal number.
Is τ(G) ≤ n - ω(n)√n for some function ω(n) → ∞?

OPEN

*Reference:* [erdosproblems.com/610](https://www.erdosproblems.com/610)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos610

variable {α : Type*} [Fintype α]

/-- Clique transversal number -/
noncomputable def cliqueTransversal (G : SimpleGraph α) : ℕ := sorry

/-- τ(G) ≤ n - ω(n)√n for some ω → ∞ -/
@[category research open, AMS 05]
theorem clique_transversal_bound (answer : Prop) :
    answer ↔ ∃ (ω : ℕ → ℝ), Filter.Tendsto ω Filter.atTop Filter.atTop ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (cliqueTransversal G : ℝ) ≤ (n : ℝ) - ω n * Real.sqrt n := by
  sorry

end Erdos610
