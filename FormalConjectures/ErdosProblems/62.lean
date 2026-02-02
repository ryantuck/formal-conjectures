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
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Erdős Problem 62

*Reference:* [erdosproblems.com/62](https://www.erdosproblems.com/62)
-/

namespace Erdos62

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
If $G_1,G_2$ are two graphs with chromatic number $\aleph_1$ then must there exist a graph $G$
whose chromatic number is $4$ (or even $\aleph_0$) which is a subgraph of both $G_1$ and $G_2$?
-/
@[category research open, AMS 05]
theorem erdos_62 : answer(sorry) ↔ ∀ (V₁ V₂ : Type*) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    cardinalChromaticNumber G₁ = aleph 1 →
    cardinalChromaticNumber G₂ = aleph 1 →
    ∃ (V : Type*) (G : SimpleGraph V),
    cardinalChromaticNumber G ≥ 4 ∧
    (∃ (f : G ↪g G₁), True) ∧ (∃ (f : G ↪g G₂), True) := by
  sorry

/--
The stronger version asks for chromatic number $\aleph_0$.
-/
@[category research open, AMS 05]
theorem erdos_62.variants.aleph_0 : answer(sorry) ↔ ∀ (V₁ V₂ : Type*) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    cardinalChromaticNumber G₁ = aleph 1 →
    cardinalChromaticNumber G₂ = aleph 1 →
    ∃ (V : Type*) (G : SimpleGraph V),
    cardinalChromaticNumber G ≥ aleph 0 ∧
    (∃ (f : G ↪g G₁), True) ∧ (∃ (f : G ↪g G₂), True) := by
  sorry

end Erdos62
