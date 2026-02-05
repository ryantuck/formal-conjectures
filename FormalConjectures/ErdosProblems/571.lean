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
# Erdős Problem 571

Show that for any rational α ∈ [1,2), there exists a bipartite graph G such that
the Turán number ex(n;G) grows like n^α.

OPEN

*Reference:* [erdosproblems.com/571](https://www.erdosproblems.com/571)
-/

open SimpleGraph Finset

open scoped Topology Real

namespace Erdos571

variable {α β : Type*}

/-- The Turán number ex(n; G): maximum edges in an n-vertex graph avoiding G as subgraph -/
noncomputable def extremalNumber (n : ℕ) (G : SimpleGraph α) : ℕ := sorry

/-- A graph is bipartite if its vertices can be partitioned into two independent sets -/
def IsBipartite (G : SimpleGraph α) : Prop :=
  ∃ (A B : Set α), (∀ a ∈ A, ∀ b ∈ B, a ≠ b) ∧
    (∀ v w, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A))

/-- For any rational α ∈ [1,2), there exists a bipartite graph realizing that Turán exponent -/
@[category research open, AMS 05]
theorem turan_exponent_realization (α : ℚ) (hα : 1 ≤ α ∧ α < 2) :
    ∃ (G : SimpleGraph ℕ), IsBipartite G ∧
      ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
        ∀ᶠ (n : ℕ) in Filter.atTop,
          c₁ * (n : ℝ) ^ (α : ℝ) ≤ (extremalNumber n G : ℝ) ∧
          (extremalNumber n G : ℝ) ≤ c₂ * (n : ℝ) ^ (α : ℝ) := by
  sorry

end Erdos571
