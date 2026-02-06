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
# Erdős Problem 636

Do graphs with no large cliques/independent sets contain ≫ n^(5/2) induced subgraphs?

PROVED by Kwan and Sudakov (2021)

*Reference:* [erdosproblems.com/636](https://www.erdosproblems.com/636)
-/

open SimpleGraph Finset

open scoped Topology Real

namespace Erdos636

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Clique number -/
noncomputable def cliqueNumber (G : SimpleGraph α) : ℕ := sorry

/-- Independence number -/
noncomputable def independenceNumber (G : SimpleGraph α) : ℕ := sorry

/-- Graphs with ω(G), α(G) ≤ f(n) have ≫ n^(5/2) induced subgraphs -/
@[category research solved, AMS 05]
theorem small_clique_independent_many_induced (f : ℕ → ℕ) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)),
        cliqueNumber G ≤ f n →
        independenceNumber G ≤ f n →
        sorry ≥ c * (n : ℝ) ^ (5/2) := by
  sorry

end Erdos636
