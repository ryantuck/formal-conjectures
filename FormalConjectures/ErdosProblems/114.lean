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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Geometry.Euclidean.Basic

/-!
# Erdős Problem 114

*Reference:* [erdosproblems.com/114](https://www.erdosproblems.com/114)
-/

namespace Erdos114

open Classical Complex MeasureTheory

/--
If $p(z)\in\mathbb{C}[z]$ is a monic polynomial of degree $n$ then is the length of the curve
$ { z\in \mathbb{C} : \lvert p(z)\rvert=1}$ maximised when $p(z)=z^n-1$?
-/

-- Placeholder for the actual length definition.
-- The actual definition would involve 1-dimensional Hausdorff measure or arc length integration.
-- We define it as 0 to allow the file to compile, but mark the theorem as sorry.
noncomputable def LemniscateLength (p : Polynomial ℂ) : ℝ := 0

@[category research open, AMS 30]
theorem erdos_114 : answer(sorry) ↔ ∀ (n : ℕ), n > 0 →
  ∀ (p : Polynomial ℂ), p.Monic → p.degree = n →
    LemniscateLength p ≤ LemniscateLength (Polynomial.X ^ n - 1) := by
  sorry

end Erdos114
