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
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Erdős Problem 112

*Reference:* [erdosproblems.com/112](https://www.erdosproblems.com/112)
-/

namespace Erdos112

open SimpleGraph Classical

/--
Let $k=k(n,m)$ be minimal such that any directed graph on $k$ vertices must contain either an
independent set of size $n$ or a transitive tournament of size $m$. Determine $k(n,m)$.
-/

-- We model a directed graph as a relation V → V → Prop.
-- An independent set in a directed graph is a set of vertices with no edges between them (in either direction).
-- A transitive tournament is a tournament where the relation is transitive.
-- However, "transitive tournament of size m" usually means a subset of m vertices that induces a transitive tournament.

def IsIndependentSet {V : Type*} (G : V → V → Prop) (S : Set V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G u v ∧ ¬ G v u

def IsTransitiveTournament {V : Type*} (G : V → V → Prop) (S : Set V) : Prop :=
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → (G u v ↔ ¬ G v u)) ∧ -- Tournament property on S
  (∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, G u v → G v w → G u w) -- Transitivity on S

-- Note: A transitive tournament on S can be ordered v_1, ..., v_m such that v_i -> v_j iff i < j.

def k_prop (n m k : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = k →
    ∀ (G : V → V → Prop),
      (∃ S : Set V, S.ncard = n ∧ IsIndependentSet G S) ∨
      (∃ S : Set V, S.ncard = m ∧ IsTransitiveTournament G S)

noncomputable def k (n m : ℕ) : ℕ :=
  sInf { x | k_prop n m x }

@[category research open, AMS 05]
theorem erdos_112 : answer(sorry) ↔ k 5 5 = sorry := by
  sorry

end Erdos112
