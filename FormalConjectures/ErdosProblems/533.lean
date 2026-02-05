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

/-!
# Erdős Problem 533

Let δ > 0. If n is sufficiently large and G is a graph on n vertices with no K₅
and at least δn² edges, does G contain a set of ≫_δ n vertices with no triangle?

Equivalently: Is δ₃(5) = 0?

DISPROVED: Balogh-Lenz showed δ₃(5) > 0. The correct value is δ₃(5) = 1/12.

*Reference:* [erdosproblems.com/533](https://www.erdosproblems.com/533)
-/

open Finset

namespace Erdos533

/-- Ramsey-Turán number δ₃(5) -/
noncomputable def delta_3_5 : ℝ :=
  sSup {δ : ℝ | ∃ c > 0, ∀ᶠ n in Filter.atTop, ∀ (G : SimpleGraph (Fin n)),
    G.CliqueFree 5 → (Nat.card G.edgeSet ≥ ⌊δ * n ^ 2⌋₊) →
    ∃ (S : Finset (Fin n)), S.card ≥ ⌊c * n⌋₊ ∧ (G.induce S).CliqueFree 3}

/-- The Ramsey-Turán number δ₃(5) equals 1/12 -/
@[category research solved, AMS 05]
theorem delta_3_5_value :
    delta_3_5 = 1 / 12 := by
  sorry

/-- Disproof: δ₃(5) is not zero -/
@[category research solved, AMS 05]
theorem delta_3_5_positive :
    answer(False) ↔ delta_3_5 = 0 := by
  sorry

end Erdos533
