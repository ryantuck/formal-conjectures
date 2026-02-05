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
# Erdős Problem 568

*Reference:* [erdosproblems.com/568](https://www.erdosproblems.com/568)

## Statement (OPEN)
Let G be a graph such that R(G,T_n) ≪ n for any tree T_n on n vertices
and R(G,K_n) ≪ n^2. Is it true that for any H with m edges and no isolated vertices,
R(G,H) ≪ m?

This asks whether G possesses "Ramsey size linearity."

## Source
[EFRS93]
-/

open SimpleGraph

open scoped Topology Real

namespace Erdos568

variable {α β : Type*}

/-- Ramsey number R(G,H) -/
def ramseyNumber (G : SimpleGraph α) (H : SimpleGraph β) : ℕ := sorry

/-- A graph is a tree if it's connected and acyclic -/
def IsTree (G : SimpleGraph α) : Prop := G.Connected ∧ ∀ (v w : α), ∃! p : G.Walk v w, p.IsPath

/-- Main conjecture: Ramsey size linearity -/
@[category research open, AMS 05]
theorem ramsey_size_linearity
    (G : SimpleGraph α)
    (h_tree : ∀ n : ℕ, ∀ T : SimpleGraph (Fin n), IsTree T →
      ∃ c : ℝ, ∀ n' ≥ n, (ramseyNumber G T : ℝ) ≤ c * n')
    (h_complete : ∀ n : ℕ, ∃ c : ℝ, (ramseyNumber G (completeGraph (Fin n)) : ℝ) ≤ c * n^2) :
    ∀ (H : SimpleGraph β) (m : ℕ) (h_edges : H.edgeSet.ncard = m)
      (h_no_isolated : ∀ v, ∃ w, H.Adj v w),
    ∃ c : ℝ, (ramseyNumber G H : ℝ) ≤ c * m :=
  sorry

end Erdos568
