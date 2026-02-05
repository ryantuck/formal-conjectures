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
# Erdős Problem 515

Let f(z) be an entire function, not a polynomial. Does there exist a locally rectifiable
path C tending to infinity such that, for every positive lambda, the integral
of |f(z)|^{-lambda} along C is finite?

SOLVED: Lewis, Rossi, and Weitsman (1984) proved the general case.

*Reference:* [erdosproblems.com/515](https://www.erdosproblems.com/515)
-/

open Topology Filter MeasureTheory Complex

namespace Erdos515

/-- Rectifiable paths with controlled integral decay for entire functions -/
@[category research solved, AMS 30]
theorem rectifiable_decay_path :
    ∀ (f : ℂ → ℂ), Differentiable ℂ f →
      (∀ (p : Polynomial ℂ), ∃ z : ℂ, f z ≠ p.eval z) →
      ∃ (C : ℝ → ℂ), Continuous C ∧ Tendsto (‖C ·‖) atTop atTop ∧
        ∀ (lam : ℝ), lam > 0 → ∃ I : ℝ, ∀ t : ℝ,
          ∫ s in (0:ℝ)..t, ‖f (C s)‖ ^ (-lam) ≤ I := by
  sorry

end Erdos515
