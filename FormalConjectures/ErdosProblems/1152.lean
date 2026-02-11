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
# Erdős Problem 1152

Non-convergent interpolating polynomials.

OPEN

*Reference:* [erdosproblems.com/1152](https://www.erdosproblems.com/1152)
-/

open Finset Filter MeasureTheory

open scoped Topology Real

namespace Erdos1152

/-- Non-convergent interpolating polynomials -/
@[category research open, AMS 41]
theorem non_convergent_interpolating_polynomials (answer : Prop) :
    answer ↔ ∀ (nodes : (n : ℕ) → Fin n → ℝ) (ε : ℕ → ℝ),
      (∀ n i, nodes n i ∈ Set.Icc (-1 : ℝ) 1) →
      (∀ n i j, i ≠ j → nodes n i ≠ nodes n j) →
      Tendsto ε atTop (𝓝 0) →
      ∃ (f : ℝ → ℝ), Continuous f ∧
        ∀ (p : ℕ → Polynomial ℝ),
          (∀ n, (p n).natDegree < (1 + ε n) * n) →
          (∀ n i, (p n).eval (nodes n i) = f (nodes n i)) →
          ∃ᵐ x ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)),
            ¬ Tendsto (fun n => (p n).eval x) atTop (𝓝 (f x)) := by
  sorry

end Erdos1152
