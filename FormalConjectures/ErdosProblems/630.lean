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
# Erdős Problem 630

Does every planar bipartite graph have list chromatic number χ_L(G) ≤ 3?

PROVED by Alon and Tarsi (1992)

*Reference:* [erdosproblems.com/630](https://www.erdosproblems.com/630)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos630

variable {α : Type*}

/-- List chromatic number -/
noncomputable def listChromaticNumber (G : SimpleGraph α) : ℕ := sorry

/-- A graph is planar -/
def IsPlanar (G : SimpleGraph α) : Prop := sorry

/-- A graph is bipartite -/
def IsBipartite (G : SimpleGraph α) : Prop :=
  ∃ (A B : Set α), (∀ a ∈ A, ∀ b ∈ B, a ≠ b) ∧
    (∀ v w, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A))

/-- Every planar bipartite graph has χ_L(G) ≤ 3 -/
@[category research solved, AMS 05]
theorem planar_bipartite_list_chromatic (G : SimpleGraph α)
    (hplanar : IsPlanar G) (hbipartite : IsBipartite G) :
    listChromaticNumber G ≤ 3 := by
  sorry

end Erdos630
