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
# Erdős Problem 1156

Concentration of chromatic number in random graphs.

OPEN

*Reference:* [erdosproblems.com/1156](https://www.erdosproblems.com/1156)
-/

open Finset Filter SimpleGraph

open scoped Topology Real

namespace Erdos1156

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Question 1: For random graphs G on n vertices (each edge included with probability 1/2),
    does there exist a constant C such that the chromatic number χ(G) is almost surely
    concentrated on at most C values?

    This formulation asks whether the chromatic number can be bounded to lie within
    a fixed-size interval for large n.

    NOTE: This formulation is incomplete as it lacks the actual chromatic number
    property and probability measure. A proper formalization would require defining
    the random graph model and probabilistic concentration. The chromatic number
    has type ℕ∞ (extended naturals) to handle the infinite case. -/
@[category research open, AMS 05]
theorem chromatic_concentration_bounded_range :
    answer(sorry) ↔
      (∃ (C : ℕ), ∀ᶠ (n : ℕ) in atTop,
        ∃ (S : Finset ℕ∞), S.card ≤ C ∧
          ∀ (G : SimpleGraph (Fin n)), G.chromaticNumber ∈ S) := by
  sorry

/-- Question 2: If ω(n) → ∞ sufficiently slowly, for every function f(n),
    does P(|χ(G) - f(n)| < ω(n)) < 1/2 when n is large?

    This asks whether the chromatic number resists concentration around any function.

    NOTE: This formulation is incomplete as it lacks the actual probability condition.
    A proper formalization would require defining the random graph model and
    showing that the probability of concentration around f is bounded away from 1.
    Chromatic number has type ℕ∞, so distance/difference requires careful handling. -/
@[category research open, AMS 05]
theorem chromatic_resists_concentration :
    answer(sorry) ↔
      ∀ (ω : ℕ → ℝ), (∀ᶠ (n : ℕ) in atTop, ω n > 0) →
      Tendsto ω atTop atTop →
      ∀ (f : ℕ → ℕ∞), ∃ᶠ (n : ℕ) in atTop,
        ∃ (G : SimpleGraph (Fin n)), True := by
  sorry

end Erdos1156
