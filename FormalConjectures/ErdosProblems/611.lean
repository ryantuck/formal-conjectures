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
# Erdős Problem 611

For a graph G on n vertices with all maximal cliques having at least cn vertices,
is τ(G) = o_c(n)?

OPEN

*Reference:* [erdosproblems.com/611](https://www.erdosproblems.com/611)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos611

variable {α : Type*} [Fintype α]

/-- Clique transversal number -/
noncomputable def cliqueTransversal (G : SimpleGraph α) : ℕ := sorry

/-- Large minimal cliques imply τ(G) = o(n) -/
@[category research open, AMS 05]
theorem large_cliques_small_transversal (c : ℝ) (hc : 0 < c ∧ c < 1) (answer : Prop) :
    answer ↔ ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)),
        (∀ (clique : Finset (Fin n)), sorry → clique.card ≥ Nat.floor (c * n)) →
        (cliqueTransversal G : ℝ) < ε * (n : ℝ) := by
  sorry

end Erdos611
