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
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Nat.Lattice

@[expose] public section

/-!
# Graph Ramsey Numbers

This file defines the classical 2-color graph Ramsey number `R(k, l)`, the diagonal graph
Ramsey number `R(H)` for a given graph `H`, and the diagonal Ramsey number `R(k)`.
-/

namespace SimpleGraph

/-- The 2-color graph Ramsey number `R(k, l)`: the minimum `N` such that every simple graph
on `N` vertices contains either a `k`-clique or an `l`-clique in the complement
(equivalently, an independent set of size `l`). -/
noncomputable def ramseyNumber (k l : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree k ∨ ¬Gᶜ.CliqueFree l}

/-- The diagonal graph Ramsey number `R(H)`: the minimum `N` such that every simple
graph `G` on `N` vertices either contains a copy of `H` as a subgraph or its
complement contains a copy of `H`. -/
noncomputable def graphRamseyNumber {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    H.IsContained G ∨ H.IsContained Gᶜ}

/-- The classical diagonal Ramsey number `R(k) := R(K_k, K_k)`. -/
noncomputable def diagRamseyNumber (k : ℕ) : ℕ :=
  graphRamseyNumber (⊤ : SimpleGraph (Fin k))

end SimpleGraph
