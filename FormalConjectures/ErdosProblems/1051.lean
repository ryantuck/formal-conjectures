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
# Erdős Problem 1051

STATUS: SOLVED

*Reference:* [erdosproblems.com/1051](https://www.erdosproblems.com/1051)
-/

namespace Erdos1051

/--
English version: A sequence of integers `a` satisfies the growth condition if
$\liminf a_n^{\frac{1}{2^n}} > 1$.
-/
def GrowthCondition (a : ℕ → ℤ) : Prop :=
  Filter.liminf (fun n => ((a n : ℝ) ^ (1 / 2 ^ n : ℝ))) Filter.atTop > 1

/--
English version: -/
@[category research open, AMS 11]
theorem erdos_1051 :
    answer(sorry) ↔ ∀ (a : ℕ → ℤ), StrictMono a → GrowthCondition a →
      Irrational (ErdosSeries a) := by
  sorry

/--
English version: Erdős [Er88c] notes that if the sequence grows rapidly to infinity (specifically, if
$a_{n+1} \geq C \cdot a_n^2$ for some constant $C > 0$), then the series is irrational.

[Er88c] Erdős, P., _On the irrationality of certain series: problems and results_.
New advances in transcendence theory (Durham, 1986) (1988), 102-109.
-/@[category research solved, AMS 11]
theorem erdos_1051.rapid_growth (a : ℕ → ℤ) (h_mono : StrictMono a)
    (h_rapid : ∃ C > 0, ∀ n, (a (n + 1) : ℝ) ≥ C * (a n : ℝ) ^ 2) :
    Irrational (ErdosSeries a) := by
  sorry

end Erdos1051
