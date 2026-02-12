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
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Erdős Problem 1040

Logarithmic capacity and level sets.

DISPROVED

STATUS: SOLVED

*Reference:* [erdosproblems.com/1040](https://www.erdosproblems.com/1040)
-/

open Finset MeasureTheory

open scoped Topology Real Classical

namespace Erdos1040

/--
English version:  Measure of polynomial level set -/
noncomputable def μ (F : Set ℂ) : ℝ :=
  iInf (fun (roots : Multiset ℂ) =>
    if roots.toFinset.toSet ⊆ F then
      let p := roots.map (fun z => Polynomial.X - Polynomial.C z) |>.prod
      (volume {z : ℂ | ‖p.eval z‖ < 1}).toReal
    else (0 : ℝ) / 0) -- Using NaN for infinity if Top is not available

/--
English version: Transfinite diameter of a set in the complex plane -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  iSup (fun (n : ℕ) =>
    if n ≥ 2 then
      iSup (fun (z : Fin n → ℂ) =>
        if (∀ i, z i ∈ F) then
          (∏ i, ∏ j ∈ filter (· < i) univ, ‖z i - z j‖) ^ (2 / (n * (n - 1) : ℝ))
        else 0)
    else 0)

/--
English version:  -/
@[category research open, AMS 30]
theorem logarithmic_capacity : answer(False) ↔ ∀ (F : Set ℂ), IsClosed F →
      ∃ (f : ℝ → ℝ), μ F = f (transfiniteDiameter F) := by
  sorry

end Erdos1040
