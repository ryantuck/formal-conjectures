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
# Erdős Problem 625

For random graphs G(n,1/2), does χ(G) - ζ(G) → ∞, where χ is the chromatic number
and ζ is the cochromatic number?

OPEN ($1000 prize for proof that the statement is false)

*Reference:* [erdosproblems.com/625](https://www.erdosproblems.com/625)
-/

open MeasureTheory ProbabilityTheory SimpleGraph Filter Topology

open scoped Topology Real

namespace Erdos625

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Chromatic number -/
noncomputable def chromaticNumber {α : Type*} (G : SimpleGraph α) : ℕ := sorry

/-- Cochromatic number -/
noncomputable def cochromaticNumber {α : Type*} (G : SimpleGraph α) : ℕ := sorry

/-- χ(G) - ζ(G) → ∞ for random G(n,1/2) -/
@[category research open, AMS 05]
theorem chromatic_cochromatic_diverges (answer : Prop) :
    answer ↔ ∀ (G : (n : ℕ) → Ω → SimpleGraph (Fin n)),
      (∀ n (i j : Fin n), i ≠ j → ℙ {ω | (G n ω).Adj i j} = 1 / 2) →
      ∀ ε > 0, ∀ᶠ n in Filter.atTop, ∀ᵐ ω ∂ℙ,
        (chromaticNumber (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) > ε := by
  sorry

end Erdos625
