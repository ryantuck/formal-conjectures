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

/-!
# Erdős Problem 76

*Reference:* [erdosproblems.com/76](https://www.erdosproblems.com/76)
-/

namespace Erdos76

open SimpleGraph Sym2

/--
Is it true that in any $2$-colouring of the edges of $K_n$ there must exist at least
$$(1+o(1))\frac{n^2}{12}$$
many edge-disjoint monochromatic triangles?
-/
@[category research open, AMS 05]
theorem erdos_76 : answer(sorry) ↔ ∀ (ε : ℝ), 0 < ε → ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
    ∀ (c : Sym2 (Fin n) → Fin 2),
    let isMono (t : Finset (Fin n)) := t.card = 3 ∧
      ∃ (i : Fin 2), ∀ x ∈ t, ∀ y ∈ t, x ≠ y → c s(x, y) = i
    ∃ (T : Finset (Finset (Fin n))),
      (∀ t ∈ T, isMono t) ∧
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ →
        ∀ e : Sym2 (Fin n), e ∈ (completeGraph (Fin n)).edgeFinset →
        (∃ x ∈ t₁, ∃ y ∈ t₁, s(x, y) = e) →
        (∃ u ∈ t₂, ∃ v ∈ t₂, s(u, v) = e) → False) ∧
      (T.card : ℝ) ≥ (1 - ε) * (n : ℝ) ^ 2 / 12 := by
  sorry

end Erdos76