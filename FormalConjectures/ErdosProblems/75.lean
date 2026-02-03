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
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Erdős Problem 75

*Reference:* [erdosproblems.com/75](https://www.erdosproblems.com/75)
-/

namespace Erdos75

open SimpleGraph Cardinal

/--
A graph is $\kappa$-colorable if there exists a coloring with $\kappa$ colors.
-/
def IsCardinalColorable {V : Type*} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ (K : Type*) (c : V → K), Cardinal.mk K ≤ κ ∧ ∀ {u v : V}, G.Adj u v → c u ≠ c v

/--
The cardinal chromatic number of a graph.
-/
noncomputable def cardinalChromaticNumber {V : Type*} (G : SimpleGraph V) : Cardinal :=
  iInf fun κ : {κ // IsCardinalColorable G κ} ↦ κ.val

/--
Is there a graph of chromatic number $\aleph_1$ with $\aleph_1$ vertices such that for all
$\epsilon>0$ if $n$ is sufficiently large and $H$ is a subgraph on $n$ vertices then $H$
contains an independent set of size $>n^{1-\epsilon}$?
-/
@[category research open, AMS 05]
theorem erdos_75 : answer(sorry) ↔ ∃ (V : Type*) (G : SimpleGraph V),
    Cardinal.mk V = aleph 1 ∧ cardinalChromaticNumber G = aleph 1 ∧
    ∀ (ε : ℝ), 0 < ε → ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    ∀ (S : Finset V), S.card = n →
    let H := G.induce ↑S
    ∃ (I : Finset S), H.IsIndepSet (I : Set S) ∧ (I.card : ℝ) > (n : ℝ) ^ (1 - ε) := by
  sorry

end Erdos75