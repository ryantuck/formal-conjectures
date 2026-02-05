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
# Erdős Problem 512: Littlewood's Conjecture

For a finite set A ⊂ ℤ of size N, determine whether:
∫₀¹ |∑_{n ∈ A} e^{2πinθ}| dθ ≫ log N

SOLVED: Independently proved by Konyagin (1981) and McGehee, Pigno, and Smith (1981).

*Reference:* [erdosproblems.com/512](https://www.erdosproblems.com/512)
-/

open Real MeasureTheory Filter BigOperators

namespace Erdos512

/-- Littlewood's conjecture on exponential sums over finite integer sets -/
@[category research solved, AMS 42]
theorem littlewood_conjecture :
    ∃ c > 0, ∀ (A : Finset ℤ), A.Nonempty →
      ∫ θ in (0:ℝ)..(1:ℝ), ‖∑ n ∈ A, Complex.exp (2 * π * Complex.I * n * θ)‖ ≥
        c * Real.log A.card := by
  sorry

end Erdos512
