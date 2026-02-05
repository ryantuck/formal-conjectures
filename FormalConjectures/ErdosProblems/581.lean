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
# Erdős Problem 581

Let f(m) be the maximum k such that every triangle-free graph on m edges must contain
a bipartite subgraph with at least k edges. Alon showed f(m) = m/2 + Θ(m^{4/5}).

SOLVED by Alon (1996)

*Reference:* [erdosproblems.com/581](https://www.erdosproblems.com/581)
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos581

variable {α : Type*}

/-- A graph is bipartite -/
def IsBipartite (G : SimpleGraph α) : Prop :=
  ∃ (A B : Set α), (∀ a ∈ A, ∀ b ∈ B, a ≠ b) ∧
    (∀ v w, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A))

/-- f(m): max guaranteed bipartite subgraph size in triangle-free graphs with m edges -/
noncomputable def maxBipartiteSubgraph (m : ℕ) : ℕ := sorry

/-- Alon's theorem: f(m) = m/2 + Θ(m^{4/5}) -/
@[category research solved, AMS 05]
theorem alon_bipartite_subgraph (m : ℕ) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      (m : ℝ) / 2 + c₁ * (m : ℝ) ^ (4 / 5) ≤ maxBipartiteSubgraph m ∧
      maxBipartiteSubgraph m ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ (4 / 5) := by
  sorry

end Erdos581
