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
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Erdős Problem 207

*Reference:* [erdosproblems.com/207](https://www.erdosproblems.com/207)
-/

open Filter
open scoped Topology

namespace Erdos207

/--
A 3-uniform hypergraph on $V$.
-/
structure Hypergraph (V : Type*) where
  edges : Set (Finset V)
  uniform : ∀ e ∈ edges, e.card = 3

/--
A Steiner triple system on $V$ is a 3-uniform hypergraph such that every pair of distinct vertices
is contained in exactly one edge.
-/
def IsSteinerTripleSystem {V : Type*} [DecidableEq V] [Fintype V] (H : Hypergraph V) : Prop :=
  ∀ v1 v2 : V, v1 ≠ v2 → ∃! e ∈ H.edges, v1 ∈ e ∧ v2 ∈ e

/--
The condition that for any $2 \le j \le g$, any collection of $j$ edges contains at least $j+3$ vertices.
-/
def IsSparse {V : Type*} [DecidableEq V] [Fintype V] (H : Hypergraph V) (g : ℕ) : Prop :=
  ∀ (S : Finset (Finset V)), S.toSet ⊆ H.edges → 2 ≤ S.card → S.card ≤ g →
    (S.sup id).card ≥ S.card + 3

/--
For any $g \ge 2$, if $n$ is sufficiently large and $n \equiv 1, 3 \pmod 6$,
there exists a Steiner triple system on $n$ vertices with girth condition $g$.

Proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b].

[KSSS22b] Kwan, M., Sah, A., Sawhney, M., and Simkin, M., _High-girth Steiner triple systems_,
arXiv:2201.04554 (2022).
-/
@[category research solved, AMS 05]
theorem erdos_207 (g : ℕ) (hg : g ≥ 2) : ∀ᶠ (n : ℕ) in atTop,
    (n % 6 = 1 ∨ n % 6 = 3) →
    ∃ (V : Type) (_ : DecidableEq V) (_ : Fintype V) (_ : Fintype.card V = n),
      ∃ (H : Hypergraph V), IsSteinerTripleSystem H ∧ IsSparse H g := by
  sorry

end Erdos207
