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
# Erdős Problem 593

Characterize those finite 3-uniform hypergraphs which appear as subhypergraphs in every
3-uniform hypergraph of chromatic number greater than ℵ₀.

OPEN

*Reference:* [erdosproblems.com/593](https://www.erdosproblems.com/593)
-/

open Cardinal

open scoped Topology Real

namespace Erdos593

/-- 3-uniform hypergraph (edges have size exactly 3) -/
structure ThreeUniformHypergraph (α : Type*) where
  edges : Set (Finset α)
  uniform : ∀ e ∈ edges, e.card = 3

/-- Chromatic number of a 3-uniform hypergraph -/
noncomputable def chromaticNumber {α : Type*} (H : ThreeUniformHypergraph α) : Cardinal := sorry

/-- Characterize finite 3-uniform hypergraphs in all uncountably chromatic ones -/
@[category research open, AMS 03 05]
theorem characterize_finite_three_uniform_in_uncountable :
    ∃ (S : Set (ThreeUniformHypergraph ℕ)),
      ∀ (H : ThreeUniformHypergraph ℕ), H ∈ S ↔
        (Finite H.edges ∧
         ∀ (K : ThreeUniformHypergraph (Ordinal.{0})),
           chromaticNumber K > aleph0 →
           ∃ (f : ℕ ↪ Ordinal.{0}), sorry) := by
  sorry

end Erdos593
