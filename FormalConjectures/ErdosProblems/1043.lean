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
# Erdős Problem 1043

STATUS: SOLVED

*Reference:* [erdosproblems.com/1043](https://www.erdosproblems.com/1043)
-/

namespace Erdos1043

open MeasureTheory Polynomial

/--
English version:  The set $\{ z \in \mathbb{C} : \lvert f(z)\rvert\leq 1\}$ -/
def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

/--
English version: -/
@[category research solved, AMS 28 30]
theorem erdos_1043 :
    answer(False) ↔ ∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
      volume ((ℝ ∙ u).orthogonalProjection '' levelSet f) ≤ 2 := by
  sorry

/--
English version: On the other hand, Pommerenke also proved there always exists a line such that the projection has
measure at most 3.3.
-/@[category research solved, AMS 28 30]
theorem erdos_1043.variants.weak :
    ∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
      volume ((ℝ ∙ u).orthogonalProjection '' levelSet f) ≤ 3.3 := by
  sorry

end Erdos1043
