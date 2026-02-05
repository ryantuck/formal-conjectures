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
# Erdős Problem 575

If F is a finite family of finite graphs containing at least one bipartite graph,
must there exist some bipartite graph G ∈ F such that ex(n; G) ≪ ex(n; F)?

OPEN

*Reference:* [erdosproblems.com/575](https://www.erdosproblems.com/575)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos575

variable {α : Type*}

/-- The Turán number ex(n; F): maximum edges avoiding all graphs in F -/
noncomputable def extremalNumber (n : ℕ) (F : Set (SimpleGraph α)) : ℕ := sorry

/-- A graph is bipartite if its vertices partition into two independent sets -/
def IsBipartite (G : SimpleGraph α) : Prop :=
  ∃ (A B : Set α), (∀ a ∈ A, ∀ b ∈ B, a ≠ b) ∧
    (∀ v w, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A))

/-- If F contains a bipartite graph, some bipartite G ∈ F dominates ex(n; F) -/
@[category research open, AMS 05]
theorem bipartite_dominates_extremal (F : Finset (SimpleGraph ℕ))
    (h_bipartite : ∃ G ∈ F, IsBipartite G) :
    ∃ (G : SimpleGraph ℕ) (hG : G ∈ F), IsBipartite G ∧
      ∃ c : ℝ, c > 0 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
        (extremalNumber n F.toSet : ℝ) ≤ c * (extremalNumber n {G} : ℝ) := by
  sorry

end Erdos575
