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
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Erdős Problem 173

*Reference:* [erdosproblems.com/173](https://www.erdosproblems.com/173)

In any 2-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$, there is a
monochromatic congruent copy of $T$.
-/

namespace Erdos173

open EuclideanGeometry

/--
A triangle $T$ in $\mathbb{R}^2$ is a set of three points $\{a, b, c\}$.
Two triangles are congruent if there is an isometry of $\mathbb{R}^2$ mapping one to the other.
-/
def IsCongruent (T₁ T₂ : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (φ : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)), φ '' T₁ = T₂

/--
In any 2-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$, there is a
monochromatic congruent copy of $T$.
-/
@[category research open, AMS 5 05]
theorem erdos_173 :
    ∀ (f : EuclideanSpace ℝ (Fin 2) → Fin 2),
    ∃ (T₀ : Set (EuclideanSpace ℝ (Fin 2))),
    (T₀.Countable ∧ T₀.ncard = 3) → -- triangle is a set of 3 points
    ∀ (T : Set (EuclideanSpace ℝ (Fin 2))),
    (T.Countable ∧ T.ncard = 3) → -- triangle is a set of 3 points
    ¬IsCongruent T T₀ →
    ∃ (T' : Set (EuclideanSpace ℝ (Fin 2))),
    IsCongruent T' T ∧ (∀ x ∈ T', ∀ y ∈ T', f x = f y) := by
  sorry

end Erdos173
