/-
Copyright 2025 The Formal Conjectures Authors.

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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 151

*Reference:* [erdosproblems.com/151](https://www.erdosproblems.com/151)
-/

namespace Erdos151

open SimpleGraph Finset Real Classical

/--
A set S is a clique transversal if it intersects every maximal clique of size at least 2.
-/
def IsMaximalClique {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsClique S ∧ ∀ S', S ⊆ S' → G.IsClique S' → S = S'

def IsCliqueTransversal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ K : Finset V, IsMaximalClique G (K : Set V) → K.card ≥ 2 → (S ∩ K).Nonempty

/--
τ(G) is the minimal size of a clique transversal.
-/
noncomputable def tau {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf { k | ∃ S, IsCliqueTransversal G S ∧ S.card = k }

/--
The independence number of G.
-/
def IsIndependentSet {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y

noncomputable def alpha {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup (univ : Finset (Finset V)) (fun (S : Finset V) => if IsIndependentSet G (S : Set V) then S.card else 0)

/--
H(n) is the minimal independence number among all triangle-free graphs on n vertices.
-/
noncomputable def H (n : ℕ) : ℕ :=
  sInf { k | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    G.CliqueFree 3 ∧ k = alpha G }

/--
The conjecture is that τ(G) ≤ n - H(n).
-/
@[category research open, AMS 05]
theorem erdos_151 :
    answer(sorry) ↔ ∀ n, ∀ (G : SimpleGraph (Fin n)),
      tau G ≤ n - H n := by
  sorry

end Erdos151
