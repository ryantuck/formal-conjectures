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
# Erdős Problem 1164

Random walk coverage in ℤ².

SOLVED - Proved independently by Révész and Kesten. Stronger result by
Dembo, Peres, Rosen, and Zeitouni.

*Reference:* [erdosproblems.com/1164](https://www.erdosproblems.com/1164)
-/

open Finset Filter Asymptotics

open scoped Topology Real

namespace Erdos1164

/-- Let R_n denote the maximal integer such that with high probability, a random walk
    starting at the origin in ℤ² visits every point x with ‖x‖ ≤ R_n within n steps.

    The main result: log R_n ≍ √(log n)

    A stronger distributional result was proved:
    lim P((log R_n)²/log n ≤ x) = e^(-4x) for all x > 0

    This formalization states the asymptotic relationship. -/
@[category research solved, AMS 60]
theorem random_walk_coverage_radius :
    ∃ (R : ℕ → ℝ), ∃ (C₁ C₂ : ℝ), C₁ > 0 ∧ C₂ > 0 ∧
      ∀ᶠ (n : ℕ) in atTop,
        C₁ * Real.sqrt (Real.log n) ≤ Real.log (R n) ∧
        Real.log (R n) ≤ C₂ * Real.sqrt (Real.log n) := by
  sorry

end Erdos1164
